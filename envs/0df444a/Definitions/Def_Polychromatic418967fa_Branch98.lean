-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch98
-- name    : Polychromatic418967fa_Branch98
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:49.675729+00:00
-- url     : https://prove2.me/theorems/75bbfa41-89ff-4697-9d8c-eab41f02dc33
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

def Polychromatic418967fa.branch_98 : allB 98 98 :=
  allB_succ' 2 97 98 (Eq.refl Bool.true) (allA_of_3_0 2 97 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3 96
  98 (Eq.refl Bool.true) (allA_succ_of_gcd 2 96 98 2 1 48 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 96 98 (accept_3_2 1 96 98 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 98))) (allB_succ' 4 95 98 (Eq.refl Bool.true) (allA_succ_of_accept 3 95 98
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 95 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 98 (accept_3_2 1 95 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 98)))) (allB_succ' 5 94 98 (Eq.refl Bool.true) (allA_of_3_0 5 94 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 93 98 (Eq.refl Bool.true) (allA_succ_of_accept 5 93 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 98 (accept_3_2 4 93 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 93 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 98 (accept_3_2 1 93 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93 98)))))) (allB_succ' 7 92 98 (Eq.refl Bool.true) (allA_succ_of_gcd 6 92 98 2 3 46 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92 98
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 92 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 98 2 2 46 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 98 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 92 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 98 2 1 46 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 98 (accept_3_2 1 92 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 98))))))) (allB_succ' 8 91 98 (Eq.refl Bool.true) (allA_of_3_0 8 91 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 9 90 98 (Eq.refl Bool.true) (allA_succ_of_gcd 8 90 98 2 4 45 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 98 (accept_3_2 7 90 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 98 2 3 45 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 98 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 90 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 98 2 2 45 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 98
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 90 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 98 2 1 45 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 98 (accept_3_2 1 90 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 98)))))))))
  (allB_succ' 10 89 98 (Eq.refl Bool.true) (allA_succ_of_accept 9 89 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 98
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 89 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 98 (accept_3_2 7 89 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 98
  (Polychromatic418967fa.accept_15_6_14_8_1_245 6 89 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 98 (Polychromatic418967fa.accept_13_5_11_7_1_559 5 89 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 98 (accept_3_2 4 89 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 98 (Polychromatic418967fa.accept_11_2_1_10_1_196 2
  89 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 98 (accept_3_2 1 89 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 98)))))))))) (allB_succ' 11 88 98 (Eq.refl Bool.true)
  (allA_of_3_0 11 88 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 87 98 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 98 (accept_3_2 10 87 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 98 (Polychromatic418967fa.accept_13_8_9_7_1_530 8
  87 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 98 (accept_3_2 7 87 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 98 (Polychromatic418967fa.accept_12_6_3_2_1_743 6
  87 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 98
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 98 (accept_3_2 4 87 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 98
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 98 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 87 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 98 (accept_3_2 1 87 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 98)))))))))))) (allB_succ' 13 86 98 (Eq.refl Bool.true) (allA_succ_of_gcd 12 86 98 2 6 43 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 98
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 86 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 98 2 5 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 98 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 86 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 98 2 4 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 98 (accept_3_2 7 86 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 98 2 3 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 98 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 86 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 98 2 2 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 98 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 86
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 98 2 1 43 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 98 (accept_3_2 1 86
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86 98))))))))))))) (allB_succ' 14 85 98 (Eq.refl Bool.true)
  (allA_of_3_0 14 85 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 84 98 (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 84 98 14 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 98 (accept_3_2 13 84 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 98
  2 6 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84
  98 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 98 2 5 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 84 98 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 84 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 98 2 4 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 84 98 7 1 12 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 84 98 2 3 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 98 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 98 2 2 42 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 98
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 84 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 84 98 2 1 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 98 (accept_3_2 1 84 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  98))))))))))))))) (allB_succ' 16 83 98 (Eq.refl Bool.true) (allA_succ_of_accept 15 83 98
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 83 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 98 (accept_3_2 13 83 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 83 98 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 98 (Polychromatic418967fa.accept_10_1_3_8_1_136 11
  83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 98 (accept_3_2 10 83 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 98
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 98 (accept_3_2 7 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 98
  (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 98 (accept_3_2 4 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 83 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 98 (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 83 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 98 (accept_3_2 1 83 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 83 98)))))))))))))))) (allB_succ' 17 82 98 (Eq.refl Bool.true) (allA_of_3_0
  17 82 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 81 98 (Eq.refl Bool.true) (allA_succ_of_accept 17 81
  98 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 98 (accept_3_2 16 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81
  98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 98 (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 81 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 98 (accept_3_2 13 81 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 98 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 81 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 98 (accept_3_2 10 81 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 98 (Polychromatic418967fa.accept_10_9_1_8_1_755 9
  81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 98
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 8 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 98 (accept_3_2 7 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 98
  (Polychromatic418967fa.accept_12_6_9_2_1_311 6 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 98 (accept_3_2 4 81 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 98 (Polychromatic418967fa.accept_15_2_6_8_1_754 2
  81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 98 (accept_3_2 1 81 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 98)))))))))))))))))) (allB_succ' 19 80 98 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 80 98 2 9 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 80 98 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 80 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 98 2 8 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 98 (Polychromatic418967fa.accept_21_15_17_14_1_4191 15 80 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 98 2 7 40 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 98 (accept_3_2 13 80 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 98 2 6 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 98 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  11 80 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 98 2 5 40 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 98
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 80 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 98 2 4 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 98 (accept_3_2 7 80 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 98 2
  3 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80 98
  (Polychromatic418967fa.accept_12_5_8_2_1_309 5 80 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 98 2 2 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 98 (Polychromatic418967fa.accept_15_3_5_8_1_1387 3 80 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 98 2 1 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 98 (accept_3_2 1 80 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 98))))))))))))))))))) (allB_succ' 20 79 98 (Eq.refl Bool.true) (allA_of_3_0 20 79 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 78 98 (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 98 2 10 39 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 98
  (accept_3_2 19 78 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 98 2 9 39 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 98
  (Polychromatic418967fa.accept_19_17_2_3_1_4190 17 78 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 78 98 2 8 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 78 98 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 78 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 98 2 7 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 98 (accept_3_2 13 78 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 78 98 2 6 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 78 98 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 98 2 5 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 98 (Polychromatic418967fa.accept_11_9_1_10_1_920 9
  78 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 98 2 4 39 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 98 (accept_3_2 7 78
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 98 2 3 39 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 98
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 78 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 78 98 2 2 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 78 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 78 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 98 2 1 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 98 (accept_3_2 1 78 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 98))))))))))))))))))))) (allB_succ' 22 77 98 (Eq.refl Bool.true) (allA_succ_of_gcd 21 77 98 7
  3 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 77 98
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 98 (accept_3_2 19 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77
  98 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 98 (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 77 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 98 (accept_3_2 16 77 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 77 98 7 2 11 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 77 98 (accept_3_2 13 77 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 98 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 98 (accept_3_2 10 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77
  98 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 77 98 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 77 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 77 98 7 1 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 77 98 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 98
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 98 (accept_3_2 4 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 98 (accept_3_2 1 77 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 98)))))))))))))))))))))) (allB_succ' 23 76 98 (Eq.refl Bool.true) (allA_of_3_0 23 76 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 75 98 (Eq.refl Bool.true) (allA_succ_of_accept 23 75 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 98 (accept_3_2 22 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 98 (accept_3_2 19 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 98 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 75 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 98 (accept_3_2 16 75 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 98 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 98
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 98 (accept_3_2 13 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75
  98 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 98 (accept_3_2 10 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 98 (Polychromatic418967fa.accept_11_8_9_10_1_503 8
  75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 98 (accept_3_2 7 75 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 98 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 75
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 98
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 98 (accept_3_2 4 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 98
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 98 (accept_3_2 1 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 75 98)))))))))))))))))))))))) (allB_succ' 25 74 98 (Eq.refl Bool.true) (allA_succ_of_gcd 24 74
  98 2 12 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  74 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 74 98 2 11 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 74 98 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 74 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 98 2 10 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 98 (accept_3_2 19 74 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 98 2 9 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 74 98 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 74 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 98 2 8 37 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 98
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 98 2 7 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 98 (accept_3_2 13 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 98
  2 6 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74
  98 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 98 2 5 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 98 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 74 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 98 2 4 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 98 (accept_3_2 7 74 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 98 2 3 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 74 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 98 2 2 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 98 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 74
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 98 2 1 37 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 98 (accept_3_2 1 74
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 98))))))))))))))))))))))))) (allB_succ' 26 73 98 (Eq.refl
  Bool.true) (allA_of_3_0 26 73 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 72 98 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 72 98 2 13 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 72 98 (accept_3_2 25 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 98
  2 12 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72
  98 (Polychromatic418967fa.accept_21_2_9_14_1_4189 23 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 72 98 2 11 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 72 98 (Polychromatic418967fa.accept_22_21_6_10_1_4188 21 72 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 98 2 10 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 98 (accept_3_2 19 72 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 98 2 9 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 72 98 (Polychromatic418967fa.accept_19_17_15_3_1_4174 17 72 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 98 2 8 36 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 98
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 72 98 2 7 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 98 (accept_3_2 13 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 98
  2 6 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72
  98 (Polychromatic418967fa.accept_15_11_12_8_1_739 11 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 72 98 2 5 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 72 98 (Polychromatic418967fa.accept_17_9_4_13_1_3057 9 72 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 98 2 4 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 98 (accept_3_2 7 72 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 72 98 2 3 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 72 98 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 72 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 98 2 2 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 98 (Polychromatic418967fa.accept_15_3_12_8_1_738 3
  72 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 98 2 1 36 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 98 (accept_3_2 1 72
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 98))))))))))))))))))))))))))) (allB_succ' 28 71 98 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 71 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 98 (Polychromatic418967fa.accept_11_4_5_10_1_926
  26 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 98 (accept_3_2 25 71
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 98
  (Polychromatic418967fa.accept_19_5_14_3_1_4187 24 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 71 98 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 71 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 98 (accept_3_2 22 71 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 71 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 98 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  20 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 98 (accept_3_2 19 71
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 98
  (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 71 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 98 (accept_3_2 16 71 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 71 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 98 (Polychromatic418967fa.accept_13_1_6_7_1_550 14
  71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 98 (accept_3_2 13 71 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 98 (Polychromatic418967fa.accept_13_12_6_7_1_1071
  12 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 98
  (Polychromatic418967fa.accept_16_11_7_2_1_4185 11 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 98 (accept_3_2 10 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 71 98 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 71 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 98 (accept_3_2 7 71 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 71 98 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 71 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 98 (accept_3_2 4 71 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 98
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 2 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 98 (accept_3_2 1 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  98)))))))))))))))))))))))))))) (allB_succ' 29 70 98 (Eq.refl Bool.true) (allA_of_3_0 29 70 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 69 98 (Eq.refl Bool.true) (allA_succ_of_accept 29 69 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 98 (accept_3_2 28 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69
  98 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 98 (Polychromatic418967fa.accept_19_7_12_3_1_4169 26 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 98 (accept_3_2 25 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 98 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 69 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 98 (accept_3_2 22 69 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 21
  69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 98
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 98 (accept_3_2 19 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69
  98 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 98 (accept_3_2 16 69 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 98
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 98 (accept_3_2 13 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69
  98 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 98 (accept_3_2 10 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 98 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 69 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 98 (Polychromatic418967fa.accept_21_8_6_14_1_4184 8
  69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 98 (accept_3_2 7 69 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 98 (Polychromatic418967fa.accept_12_6_9_2_1_311 6
  69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 98 (accept_3_2 4 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 98 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 98 (accept_3_2 1 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 98)))))))))))))))))))))))))))))) (allB_succ' 31 68 98 (Eq.refl Bool.true) (allA_succ_of_gcd
  30 68 98 2 15 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 68 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 68 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 98 2 14 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 98 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 68 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 98 2 13 34 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 98 (accept_3_2 25 68 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 98 2 12 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 98 (Polychromatic418967fa.accept_11_1_2_10_1_1426
  23 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 98 2 11 34 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 98
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 98 2 10 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 98 (accept_3_2 19 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 98
  2 9 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68
  98 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 68 98 2 8 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 68 98 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 68 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 98 2 7 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 98 (accept_3_2 13 68 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 68 98 2 6 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 68 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 68 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 98 2 5 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 98 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9
  68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 98 2 4 34 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 98 (accept_3_2 7 68
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 98 2 3 34 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68 98
  (Polychromatic418967fa.accept_12_5_8_2_1_309 5 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 98 2 2 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 98 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 68 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 98 2 1 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 98 (accept_3_2 1 68 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 98))))))))))))))))))))))))))))))) (allB_succ' 32 67 98 (Eq.refl Bool.true) (allA_of_3_0 32 67
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 66 98 (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 98 2 16
  33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 98
  (accept_3_2 31 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 98 2 15 33 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 98
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 98 2 14 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 66 98 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 98 2 13 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 98 (accept_3_2 25 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 66 98 2 12 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 98 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 66 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 98 2 11 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 98 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21
  66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 98 2 10 33 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 98 (accept_3_2 19 66
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 98 2 9 33 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 98
  (Polychromatic418967fa.accept_15_2_6_8_1_754 17 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 66 98 2 8 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 66 98 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 98 2 7 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 98 (accept_3_2 13 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 66 98 2 6 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 66 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 66 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 98 2 5 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 98 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9
  66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 98 2 4 33 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 98 (accept_3_2 7 66
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 98 2 3 33 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 98
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 66 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 98 2 2 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 66 98 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 98 2 1 33 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 98 (accept_3_2 1 66 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 98))))))))))))))))))))))))))))))))) (allB_succ' 34 65 98 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 65 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 98 (accept_3_2 31 65 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 98 (Polychromatic418967fa.accept_9_3_2_8_1_108 30
  65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 98
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 98 (accept_3_2 28 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65
  98 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 65 98 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 98 (accept_3_2 25 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 65 98 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 98 (accept_3_2 22 65 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 98
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 98 (accept_3_2 19 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65
  98 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 98 (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 98 (accept_3_2 16 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 65 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 98 (accept_3_2 13 65 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 98 (Polychromatic418967fa.accept_9_3_2_8_1_108 12
  65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 98 (accept_3_2 10 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65
  98 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 98 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 98 (accept_3_2 7 65 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 98 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 65 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 98 (accept_3_2 4 65 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 98
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 98 (accept_3_2 1 65 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  98)))))))))))))))))))))))))))))))))) (allB_succ' 35 64 98 (Eq.refl Bool.true) (allA_of_3_0 35 64 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 63 98 (Eq.refl Bool.true) (allA_succ_of_gcd 35 63 98 7 5 9 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 98 (accept_3_2 34 63
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 98
  (Polychromatic418967fa.accept_24_8_15_2_1_4183 32 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 98 (accept_3_2 31 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63
  98 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 98 7 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 63 98 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 63 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 98
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 98 (accept_3_2 25 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63
  98 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 98 (accept_3_2 22 63 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 63 98 7 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 63 98 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 63 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 98 (accept_3_2 19 63 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 98 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 63 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 98
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 98 (accept_3_2 16 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63
  98 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 63 98 7 2 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 63 98 (accept_3_2 13 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63
  98 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 98 (accept_3_2 10 63 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 98
  (Polychromatic418967fa.accept_19_8_6_3_1_4164 8 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 63 98 7 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 63 98 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 63 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 98 (accept_3_2 4 63 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 98 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 63 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 98
  (Polychromatic418967fa.accept_19_2_6_3_1_4182 2 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 98 (accept_3_2 1 63 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  98)))))))))))))))))))))))))))))))))))) (allB_succ' 37 62 98 (Eq.refl Bool.true) (allA_succ_of_gcd 36 62 98 2 18 31 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 98
  (Polychromatic418967fa.accept_10_5_2_8_1_135 35 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 62 98 2 17 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 62 98 (Polychromatic418967fa.accept_19_14_5_3_1_859 33 62 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 62 98 2 16 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 62 98 (accept_3_2 31 62 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 62 98 2 15 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 98 (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 62 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 98 2 14 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 98 (Polychromatic418967fa.accept_19_8_5_3_1_4181 27
  62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 98 2 13 31 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 98 (accept_3_2 25 62
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 98 2 12 31 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 98
  (Polychromatic418967fa.accept_17_6_11_13_1_4180 23 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 98 2 11 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 98 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 62 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 98 2 10 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 98 (accept_3_2 19 62 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 62 98 2 9 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 62 98 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 62 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 98 2 8 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 98 (Polychromatic418967fa.accept_10_5_2_8_1_135 15
  62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 98 2 7 31 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 98 (accept_3_2 13 62
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 98 2 6 31 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 98
  (Polychromatic418967fa.accept_21_11_20_14_1_4179 11 62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 98 2 5 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 98 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 62 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 98 2 4 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 98 (accept_3_2 7 62 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 98 2 3 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 98 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 62 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 98 2 2 31 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 98 (Polychromatic418967fa.accept_11_3_7_10_1_180 3
  62 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 98 2 1 31 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 98 (accept_3_2 1 62
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 98))))))))))))))))))))))))))))))))))))) (allB_succ' 38 61 98
  (Eq.refl Bool.true) (allA_of_3_0 38 61 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 60 98 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 60 98 2 19 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 60 98 (accept_3_2 37 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 98 2 18 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 60 98 (Polychromatic418967fa.accept_13_9_8_7_1_1073 35 60 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 98 2 17 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 98 (Polychromatic418967fa.accept_16_1_12_2_1_2136 33 60 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 98 2 16 30 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 98 (accept_3_2 31 60 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 98 2 15 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 98 (Polychromatic418967fa.accept_9_2_6_8_1_321 29
  60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 98 2 14 30 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 98
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 60 98 2 13 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 60 98 (accept_3_2 25 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 98
  2 12 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60
  98 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 98 2 11 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 60 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 98 2 10 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 98 (accept_3_2 19 60 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 60 98 2 9 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 60 98 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 60 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 98 2 8 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 98 (Polychromatic418967fa.accept_11_4_5_10_1_926 15
  60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 98 2 7 30 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 98 (accept_3_2 13 60
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 98 2 6 30 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 98
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 98 2 5 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 60 98 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 60 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 98 2 4 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 98 (accept_3_2 7 60 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 60 98 2 3 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 60 98 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 60 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 98 2 2 30 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 98 2 1 30 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 98 (accept_3_2 1 60
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 98))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 59
  98 (Eq.refl Bool.true) (allA_succ_of_accept 39 59 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 98
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 98 (accept_3_2 37 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59
  98 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 59 98 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 98 (accept_3_2 34 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 59 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 98 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  32 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 98 (accept_3_2 31 59
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 98 (Polychromatic418967fa.accept_9_3_5_8_1_99
  30 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 98
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 98 (accept_3_2 28 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 59
  98 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 59 98 (Polychromatic418967fa.accept_21_5_17_14_1_4178 26 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 98 (accept_3_2 25 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 59 98 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 98 (Polychromatic418967fa.accept_16_7_11_2_1_3117
  23 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 98 (accept_3_2 22 59
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 98
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 98 (accept_3_2 19 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59
  98 (Polychromatic418967fa.accept_19_18_2_3_1_4177 18 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 98 (accept_3_2 16 59 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 98
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 98 (accept_3_2 13 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59
  98 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 59 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 98 (accept_3_2 10 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 59 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 98 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8
  59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 98 (accept_3_2 7 59 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 98 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 59
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 98
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 98 (accept_3_2 4 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 98
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 98 (accept_3_2 1 59 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 98)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 58 98 (Eq.refl Bool.true)
  (allA_of_3_0 41 58 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 57 98 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 98 (accept_3_2 40 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 38
  57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 98 (accept_3_2 37 57 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 98 (Polychromatic418967fa.accept_17_2_6_13_1_2056
  36 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 98 (accept_3_2 34 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57
  98 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 98 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 98 (accept_3_2 31 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 98 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 57 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 98 (accept_3_2 28 57 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 98
  (Polychromatic418967fa.accept_15_11_12_8_1_739 26 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 98 (accept_3_2 25 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57
  98 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 98 (accept_3_2 22 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 98 (Polychromatic418967fa.accept_20_1_17_18_1_1678 21 57 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 20
  57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 98 (accept_3_2 19 57 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 98 (Polychromatic418967fa.accept_12_6_9_2_1_311 18
  57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 98 (accept_3_2 16 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57
  98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 98 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 98 (accept_3_2 13 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 98 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 57 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 98 (accept_3_2 10 57 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 98 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9
  57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 98
  (Polychromatic418967fa.accept_21_8_15_14_1_4176 8 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 98 (accept_3_2 7 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 98
  (Polychromatic418967fa.accept_9_6_3_8_1_595 6 57 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 98 (accept_3_2 4 57 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 57
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 98 (accept_3_2 1 57 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 98)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 56
  98 (Eq.refl Bool.true) (allA_succ_of_gcd 42 56 98 14 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 56 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 98 2 20 28 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 98
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 98 2 19 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 98 (accept_3_2 37 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 98
  2 18 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 56 98
  7 5 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 56 98 2
  17 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 98
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 98 2 16 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 98 (accept_3_2 31 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 98
  2 15 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56
  98 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 98 14 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 98 (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 56 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 98 2 13 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 98 (accept_3_2 25 56 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 56 98 2 12 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 56 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 98 2 11 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 56 98 7 3 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 56 98 2 10 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 98 (accept_3_2 19 56 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 98 2 9 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 56 98 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 56 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 98 2 8 28 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 98
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 98 14 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 98 (accept_3_2 13 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 98
  2 6 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56
  98 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 98 2 5 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 98 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 56 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 98 2 4 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 56 98 7 1 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 56 98 2 3 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 98 2 2 28 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 98
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 98 2 1 28 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 98 (accept_3_2 1 56 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  98))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 55 98 (Eq.refl Bool.true) (allA_of_3_0 44 55 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 54 98 (Eq.refl Bool.true) (allA_succ_of_gcd 44 54 98 2 22 27 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 98
  (accept_3_2 43 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 98 2 21 27 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 98
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 41 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 98 2 20 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 54 98 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 98 2 19 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 98 (accept_3_2 37 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 54 98 2 18 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 98 (Polychromatic418967fa.accept_13_9_2_7_1_1083 35 54 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 98 2 17 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 98 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33
  54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 98 2 16 27 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 98 (accept_3_2 31 54
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 98 2 15 27 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 98
  (Polychromatic418967fa.accept_10_9_4_8_1_741 29 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 98 2 14 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 54 98 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 98 2 13 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 98 (accept_3_2 25 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 54 98 2 12 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 98 (Polychromatic418967fa.accept_19_4_16_3_1_4175 23 54 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 98 2 11 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 98 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21
  54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 98 2 10 27 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 98 (accept_3_2 19 54
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 98 2 9 27 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 98
  (Polychromatic418967fa.accept_15_2_9_8_1_736 17 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 54 98 2 8 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 54 98 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 98 2 7 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 98 (accept_3_2 13 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 54 98 2 6 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 54 98 (Polychromatic418967fa.accept_16_11_6_2_1_4155 11 54 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 98 2 5 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 98 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 54
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 98 2 4 27 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 98 (accept_3_2 7 54
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 98 2 3 27 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 98
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 54 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 54 98 2 2 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 54 98 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 98 2 1 27 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 98 (accept_3_2 1 54 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 54 98))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 53 98 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 53 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 98 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 53 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 98 (accept_3_2 43 53 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 98 (Polychromatic418967fa.accept_13_3_1_7_1_1706
  42 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 98
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 98 (accept_3_2 40 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53
  98 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 98 (Polychromatic418967fa.accept_18_2_17_8_1_1893 38 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 98 (accept_3_2 37 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 98 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 98 (accept_3_2 34 53 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 98
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 98 (accept_3_2 31 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53
  98 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 53 98 (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 98 (accept_3_2 28 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 53 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 98 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  26 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 98 (accept_3_2 25 53
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 98
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 53 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 98 (accept_3_2 22 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 53 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 98 (Polychromatic418967fa.accept_12_8_5_2_1_746 20
  53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 98 (accept_3_2 19 53 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 98 (Polychromatic418967fa.accept_17_1_2_13_1_2026
  18 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 98
  (Polychromatic418967fa.accept_19_17_15_3_1_4174 17 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 98 (accept_3_2 16 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53
  98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 53 98 (Polychromatic418967fa.accept_25_14_3_23_1_4173 14 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 98 (accept_3_2 13 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 53 98 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 98 (accept_3_2 10 53 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 98
  (Polychromatic418967fa.accept_11_8_9_10_1_503 8 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 98 (accept_3_2 7 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 98
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 98 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 98 (accept_3_2 4 53 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 98 (Polychromatic418967fa.accept_18_2_17_8_1_1893 2
  53 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 98 (accept_3_2 1 53 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 98)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47
  52 98 (Eq.refl Bool.true) (allA_of_3_0 47 52 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 51 98 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 51 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 98 (accept_3_2 46 51 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 51 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 98
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 44 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 98 (accept_3_2 43 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51
  98 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 98 (accept_3_2 40 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 98 (Polychromatic418967fa.accept_9_2_6_8_1_321 38
  51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 98 (accept_3_2 37 51 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 98 (Polychromatic418967fa.accept_11_3_7_10_1_180
  36 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 98 (accept_3_2 34 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 98 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 98 (accept_3_2 31 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 98 (accept_3_2 28 51 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 98 (Polychromatic418967fa.accept_19_8_13_3_1_4172
  27 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 98
  (Polychromatic418967fa.accept_19_7_13_3_1_4171 26 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 98 (accept_3_2 25 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51
  98 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 98 (accept_3_2 22 51 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 98
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 98 (accept_3_2 19 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51
  98 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 98 (accept_3_2 16 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 98 (Polychromatic418967fa.accept_16_15_3_2_1_4170 15 51 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 98 (Polychromatic418967fa.accept_9_5_6_8_1_101 14
  51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 98 (accept_3_2 13 51 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 12
  51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 98 (accept_3_2 10 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 98 (Polychromatic418967fa.accept_13_8_12_7_1_2442 8 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 98 (accept_3_2 7 51 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 51 98 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 51 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 98 (accept_3_2 4 51 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 51
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 98
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 98 (accept_3_2 1 51 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  98)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 50 98 (Eq.refl Bool.true) (allA_succ_of_gcd 48 50 98
  2 24 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50
  98 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 98 2 23 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 50 98 (Polychromatic418967fa.accept_19_7_12_3_1_4169 45 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 98 2 22 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 98 (accept_3_2 43 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 50 98 2 21 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 50 98 (Polychromatic418967fa.accept_15_11_5_8_1_3157 41 50 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 98 2 20 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 98 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 50
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 98 2 19 25 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 98 (accept_3_2 37 50
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 98 2 18 25 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 98
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 35 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 50 98 2 17 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 50 98 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 98 2 16 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 98 (accept_3_2 31 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 50 98 2 15 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 98 2 14 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 98 (Polychromatic418967fa.accept_11_5_6_10_1_1432
  27 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 98 2 13 25 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 98 (accept_3_2 25 50
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 98 2 12 25 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 98
  (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 98 2 11 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 98 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 98 2 10 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 98 (accept_3_2 19 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 50 98 2 9 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 50 98 (Polychromatic418967fa.accept_13_4_11_7_1_558 17 50 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 98 2 8 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 98 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 98 2 7 25 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 98 (accept_3_2 13 50
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 98 2 6 25 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 98
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 98 2 5 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 98 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 98 2 4 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 98 (accept_3_2 7 50 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 98 2 3 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 98 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 50 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 98 2 2 25 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 98 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 50
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 98 2 1 25 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 98 (accept_3_2 1 50
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 98)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 98 (allA_of_3_0 49 49 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 98 (allA_succ_of_accept
  47 48 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 48 98 2 23 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 48 98 (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 48 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 98 2 22 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 98 (accept_3_2 43 48 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 98 2 21 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 48 98 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 98 2 20 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 98
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 98 2 19 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 98 (accept_3_2 37 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 98
  2 18 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48
  98 (Polychromatic418967fa.accept_15_5_3_8_1_748 35 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 98 2 17 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 48 98 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 98 2 16 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 98 (accept_3_2 31 48 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 48 98 2 15 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 48 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 98 2 14 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 98 (Polychromatic418967fa.accept_11_5_4_10_1_524 27
  48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 98 2 13 24 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 98 (accept_3_2 25 48
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 98 2 12 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 98
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 98 2 11 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 48 98 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 48 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 98 2 10 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 98 (accept_3_2 19 48 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 48 98 2 9 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 48 98 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 48 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 98 2 8 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 98 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 98 2 7 24 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 98 (accept_3_2 13 48
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 98 2 6 24 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 98
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 98 2 5 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 48 98 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 48 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 98 2 4 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 98 (accept_3_2 7 48 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 48 98 2 3 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 48 98 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 98 2 2 24 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 98 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3
  48 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 98 2 1 24 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 98 (accept_3_2 1 48
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 98)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 98 (allA_succ_of_accept 46 47 98 (accept_3_2 46 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 47 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 98 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 47 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 98 (accept_3_2 43 47 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 98 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 98
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 98 (accept_3_2 40 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47
  98 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 98 (Polychromatic418967fa.accept_13_12_8_7_1_2526 38 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 98 (accept_3_2 37 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 98 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 47 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 98 (Polychromatic418967fa.accept_10_5_7_8_1_1176
  35 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 98 (accept_3_2 34 47
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 98
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 98 (accept_3_2 31 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47
  98 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 47 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 98 (accept_3_2 28 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 47 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 98 (Polychromatic418967fa.accept_23_3_1_6_1_4168
  26 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 98 (accept_3_2 25 47
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 98 (Polychromatic418967fa.accept_9_6_2_8_1_592
  24 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 98
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 98 (accept_3_2 22 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 98 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 98 (accept_3_2 19 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 98 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 47 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 98 (accept_3_2 16 47 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 98
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 98 (accept_3_2 13 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47
  98 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 47 98 (Polychromatic418967fa.accept_19_11_9_3_1_4167 11 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 98 (accept_3_2 10 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 47 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 98 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8
  47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 98 (accept_3_2 7 47 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 98 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 47
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 98
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 98 (accept_3_2 4 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 98
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 98 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 98 (accept_3_2 1 47 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 98))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 98 (allA_of_3_0 46 46 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 98 (allA_succ_of_accept 44 45 98
  (Polychromatic418967fa.accept_19_6_7_3_1_1733 44 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 98 (accept_3_2 43 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45
  98 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 98 (accept_3_2 40 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 98 (Polychromatic418967fa.accept_13_12_6_7_1_1071
  38 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 98 (accept_3_2 37 45
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 98
  (Polychromatic418967fa.accept_20_16_5_18_1_2846 36 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 98 (accept_3_2 34 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 98 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 45 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 98 (Polychromatic418967fa.accept_10_2_5_8_1_139 32
  45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 98 (accept_3_2 31 45 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 98 (Polychromatic418967fa.accept_12_6_9_2_1_311 30
  45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 98 (accept_3_2 28 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45
  98 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 98 (Polychromatic418967fa.accept_25_1_20_23_1_4166 26 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 98 (accept_3_2 25 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 98 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 45 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 98 (accept_3_2 22 45 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 98 (Polychromatic418967fa.accept_16_5_13_2_1_2138
  21 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 98
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 98 (accept_3_2 19 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45
  98 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 98 (accept_3_2 16 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 98 (Polychromatic418967fa.accept_13_1_6_7_1_550 14
  45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 98 (accept_3_2 13 45 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 98 (Polychromatic418967fa.accept_10_2_5_8_1_139 12
  45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 98 (accept_3_2 10 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45
  98 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 98 (Polychromatic418967fa.accept_21_8_3_14_1_4165 8 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 98 (accept_3_2 7 45 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 98 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 45 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 98 (accept_3_2 4 45 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 98
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 98 (accept_3_2 1 45 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  98))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 98 (allA_succ_of_accept 43 44 98 (accept_3_2 43 44 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 98 2 21 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 98 (Polychromatic418967fa.accept_12_5_8_2_1_309 41
  44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 98 2 20 22 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 98
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 44 98 2 19 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 44 98 (accept_3_2 37 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 98
  2 18 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44
  98 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 44 98 2 17 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 44 98 (Polychromatic418967fa.accept_16_1_12_2_1_2136 33 44 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 98 2 16 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 98 (accept_3_2 31 44 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 98 2 15 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 44 98 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 44 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 98 2 14 22 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 98
  (Polychromatic418967fa.accept_19_8_6_3_1_4164 27 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 98 2 13 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 44 98 (accept_3_2 25 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 98
  2 12 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44
  98 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 44 98 2 11 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 44 98 (Polychromatic418967fa.accept_15_6_14_8_1_245 21 44 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 98 2 10 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 98 (accept_3_2 19 44 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 98 2 9 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 44 98 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 44 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 98 2 8 22 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 98
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 98 2 7 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 98 (accept_3_2 13 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 98
  2 6 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44
  98 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 98 2 5 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 98 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 44 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 98 2 4 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 98 (accept_3_2 7 44 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 44 98 2 3 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 44 98 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 44 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 98 2 2 22 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 98 (Polychromatic418967fa.accept_17_3_10_13_1_2021 3
  44 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 98 2 1 22 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 98 (accept_3_2 1 44
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 98)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  98 (allA_of_3_0 43 43 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 98 (allA_succ_of_accept 41 42 98
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 98 2 20 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 98 2 19 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 98 (accept_3_2 37 42 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 42 98 2 18 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 42 98 7 5 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 42 98 2 17 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 42 98 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 42 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 98 2 16 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 98 (accept_3_2 31 42 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 98 2 15 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 42 98 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 98 14 2 3 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 98
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 98 2 13 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 42 98 (accept_3_2 25 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 98
  2 12 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42
  98 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 98 2 11 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 42 98 7 3 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 42 98 2 10 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 98 (accept_3_2 19 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 98
  2 9 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42
  98 (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 98 2 8 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 42 98 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 42 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 98 14 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 98 (accept_3_2 13 42 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 42 98 2 6 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 42 98 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 98 2 5 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 98 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9
  42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 98 2 4 21 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 42 98 7 1 6 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 98 2 3 21 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 98
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 98 2 2 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 42 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 98 2 1 21 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 98 (accept_3_2 1 42 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 98)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 98 (allA_succ_of_accept 40 41 98
  (accept_3_2 40 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 98 (accept_3_2 37 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 98 (Polychromatic418967fa.accept_17_2_7_13_1_4163 36 41 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 98 (accept_3_2 34 41 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 98
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 98 (accept_3_2 31 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  98 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 41 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 98 (accept_3_2 28 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 41 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 98 (Polychromatic418967fa.accept_21_5_20_14_1_4162
  26 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 98 (accept_3_2 25 41
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 98 (Polychromatic418967fa.accept_9_6_5_8_1_598
  24 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 98 (accept_3_2 22 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41
  98 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 98 (accept_3_2 19 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 98 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 41 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 98 (Polychromatic418967fa.accept_16_1_9_2_1_4161
  17 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 98 (accept_3_2 16 41
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 98 (Polychromatic418967fa.accept_4_3_1_2_1_62
  15 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 98
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 98 (accept_3_2 13 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  98 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 41 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 98 (accept_3_2 10 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 41 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 98 (Polychromatic418967fa.accept_12_8_5_2_1_746 8
  41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 98 (accept_3_2 7 41 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 98 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 98
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 98 (accept_3_2 4 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 98 (accept_3_2 1 41 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 98))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 98 (allA_of_3_0 40 40 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 39 98 (allA_succ_of_accept 38 39 98
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 98 (accept_3_2 37 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39
  98 (Polychromatic418967fa.accept_19_17_1_3_1_4160 36 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 98 (accept_3_2 34 39 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 98
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 98 (accept_3_2 31 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39
  98 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 98 (accept_3_2 28 39 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 98 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 39 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 98 (Polychromatic418967fa.accept_17_9_5_13_1_2033
  26 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 98 (accept_3_2 25 39
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 98 (Polychromatic418967fa.accept_9_6_3_8_1_595
  24 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 98 (accept_3_2 22 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 39 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 98 (accept_3_2 19 39 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 98 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 39 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 98 (accept_3_2 16 39 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 98 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 98
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 98 (accept_3_2 13 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39
  98 (Polychromatic418967fa.accept_16_12_7_2_1_4159 12 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 98 (accept_3_2 10 39 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 98
  (Polychromatic418967fa.accept_17_8_5_13_1_4158 8 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 98 (accept_3_2 7 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 98
  (Polychromatic418967fa.accept_9_6_3_8_1_595 6 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 98 (accept_3_2 4 39 98 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 98 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 39 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 39 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 98 (accept_3_2 1 39 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 98))))))))))))))))))))))))))))))))))))))) (allB_succ 38 98
  (allA_succ_of_accept 37 38 98 (accept_3_2 37 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38 98
  2 18 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 38
  98 (Polychromatic418967fa.accept_16_3_6_2_1_4157 35 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 38 98 2 17 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 38 98 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 38 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 98 2 16 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 98 (accept_3_2 31 38 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 38 98 2 15 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 38 98 (Polychromatic418967fa.accept_21_8_17_14_1_4156 29 38 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 38 98 2 14 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 38 98 (Polychromatic418967fa.accept_16_11_6_2_1_4155
  27 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 98 2 13 19 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 98 (accept_3_2 25 38
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 98 2 12 19 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 98
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 38 98 2 11 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 38 98 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 38 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 98 2 10 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 98 (accept_3_2 19 38 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 38 98 2 9 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 38 98 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 38 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 98 2 8 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 98 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 98 2 7 19 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 98 (accept_3_2 13 38
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 98 2 6 19 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 98
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 38 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 98 2 5 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 98 (Polychromatic418967fa.accept_16_9_6_2_1_3101 9 38 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 98 2 4 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 98 (accept_3_2 7 38 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 98 2 3 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 38 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 98 2 2 19 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 98 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 38
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 98 2 1 19 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 98 (accept_3_2 1 38
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 98)))))))))))))))))))))))))))))))))))))) (allB_succ 37 98
  (allA_of_3_0 37 37 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 98 (allA_succ_of_accept 35 36 98
  (Polychromatic418967fa.accept_17_1_2_13_1_2026 35 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 98 2 17 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 98 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 36 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 98 2 16 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 98 (accept_3_2 31 36 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 36 98 2 15 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 36 98 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 36 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 98 2 14 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 98 (Polychromatic418967fa.accept_19_8_17_3_1_4154
  27 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 98 2 13 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 98 (accept_3_2 25 36
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 98 2 12 18 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 98
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 36 98 2 11 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 36 98 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 36 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 98 2 10 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 98 (accept_3_2 19 36 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 36 98 2 9 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 36 98 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 36 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 98 2 8 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 98 (Polychromatic418967fa.accept_17_15_2_13_1_4153
  15 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 98 2 7 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 98 (accept_3_2 13 36
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 98 2 6 18 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 98
  (Polychromatic418967fa.accept_20_11_16_18_1_2885 11 36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 98 2 5 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 36 98 (Polychromatic418967fa.accept_21_9_15_14_1_2790 9 36 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 98 2 4 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 98 (accept_3_2 7 36 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 36 98 2 3 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 36 98 (Polychromatic418967fa.accept_19_5_17_3_1_4152 5 36 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 98 2 2 18 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 98 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3
  36 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 98 2 1 18 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 98 (accept_3_2 1 36
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 98)))))))))))))))))))))))))))))))))))) (allB_succ 35 98
  (allA_succ_of_accept 34 35 98 (accept_3_2 34 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 98 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 98 (accept_3_2 31 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 98 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 35 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 35 98 7 4 5 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 35 98
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 98 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 98 (accept_3_2 25 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 98 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 35 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 98 (Polychromatic418967fa.accept_10_3_5_8_1_1132
  23 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 98 (accept_3_2 22 35
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35 98 7 3 5 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 35 98
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 98 (accept_3_2 19 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35
  98 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 98 (accept_3_2 16 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 35 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 35 98 7 2 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 98 (accept_3_2 13 35 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 98 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 35 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 98
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 98 (accept_3_2 10 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 98 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 98 7 1 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 98 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 35 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 98
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 98 (accept_3_2 4 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 98
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 98 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 98 (accept_3_2 1 35 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 98))))))))))))))))))))))))))))))))))) (allB_succ 34 98 (allA_of_3_0 34 34 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 33 98 (allA_succ_of_accept 32 33 98
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 98 (accept_3_2 31 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33
  98 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 98 (accept_3_2 28 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 98 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  26 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 98 (accept_3_2 25 33
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 98
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 98 (accept_3_2 22 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 98 (Polychromatic418967fa.accept_9_2_6_8_1_321 20
  33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 98 (accept_3_2 19 33 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 98 (Polychromatic418967fa.accept_12_6_9_2_1_311 18
  33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 98 (accept_3_2 16 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33
  98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 98 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 98 (accept_3_2 13 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 98 (accept_3_2 10 33 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 98 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9
  33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 98
  (Polychromatic418967fa.accept_19_8_14_3_1_4151 8 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 98 (accept_3_2 7 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 98
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 33 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 98 (accept_3_2 4 33 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 98 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 33
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 98 (accept_3_2 1 33 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 98))))))))))))))))))))))))))))))))) (allB_succ 32 98
  (allA_succ_of_accept 31 32 98 (accept_3_2 31 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 98
  2 15 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32
  98 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 98 2 14 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 98 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 32 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 98 2 13 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 98 (accept_3_2 25 32 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 32 98 2 12 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 32 98 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 32 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 98 2 11 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 98 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 32
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 98 2 10 16 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 98 (accept_3_2 19 32
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 98 2 9 16 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32 98
  (Polychromatic418967fa.accept_12_5_8_2_1_309 17 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 32 98 2 8 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 32 98 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 32 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 98 2 7 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 98 (accept_3_2 13 32 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 32 98 2 6 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 32 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 98 2 5 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 98 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 32
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 98 2 4 16 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 98 (accept_3_2 7 32
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 98 2 3 16 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 98
  (Polychromatic418967fa.accept_10_5_2_8_1_135 5 32 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 98 2 2 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 98 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 32 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 98 2 1 16 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 98 (accept_3_2 1 32 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 98)))))))))))))))))))))))))))))))) (allB_succ 31 98 (allA_of_3_0 31 31 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 30 98 (allA_succ_of_accept 29 30 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 98 2 14 15 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 98
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 30 98 2 13 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 98 (accept_3_2 25 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 98
  2 12 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30
  98 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 98 2 11 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 30 98 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 30 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 98 2 10 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 98 (accept_3_2 19 30 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 30 98 2 9 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 30 98 (Polychromatic418967fa.accept_20_17_10_18_1_4150 17 30 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 98 2 8 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 98 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 98 2 7 15 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 98 (accept_3_2 13 30
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 98 2 6 15 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 98
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 30 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 98 2 5 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 98 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 30 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 98 2 4 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 98 (accept_3_2 7 30 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 98 2 3 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 30 98 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 30 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 98 2 2 15 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 98 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 30
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 98 2 1 15 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 98 (accept_3_2 1 30
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 98)))))))))))))))))))))))))))))) (allB_succ 29 98
  (allA_succ_of_accept 28 29 98 (accept_3_2 28 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29
  98 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 98 (Polychromatic418967fa.accept_19_7_10_3_1_4149 26 29 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 98 (accept_3_2 25 29 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 98 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 98 (accept_3_2 22 29 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 98
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 98 (accept_3_2 19 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29
  98 (Polychromatic418967fa.accept_17_1_12_13_1_448 18 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 98 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 29 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 98 (accept_3_2 16 29 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 98
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 98 (accept_3_2 13 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29
  98 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 29 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 98 (accept_3_2 10 29 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 29 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 98 (Polychromatic418967fa.accept_12_8_5_2_1_746 8
  29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 98 (accept_3_2 7 29 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 98 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 29
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 98
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 98 (accept_3_2 4 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 98 (Polychromatic418967fa.accept_21_2_8_14_1_4148 2 29 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 98 (accept_3_2 1 29 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 98))))))))))))))))))))))))))))) (allB_succ 28 98 (allA_of_3_0 28 28 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 98 (allA_succ_of_accept 26 27 98 (Polychromatic418967fa.accept_11_4_5_10_1_926 26
  27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 98 (accept_3_2 25 27 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 98 (Polychromatic418967fa.accept_13_11_1_7_1_1691
  24 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 98 (accept_3_2 22 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 98 (Polychromatic418967fa.accept_15_5_12_8_1_3168 20 27 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 98 (accept_3_2 19 27 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 98 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 27 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 98 (accept_3_2 16 27 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 98 (Polychromatic418967fa.accept_10_5_7_8_1_1176
  15 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 98
  (Polychromatic418967fa.accept_17_14_10_13_1_4147 14 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 98 (accept_3_2 13 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27
  98 (Polychromatic418967fa.accept_21_12_6_14_1_4146 12 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 98 (accept_3_2 10 27 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 98
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 98 (accept_3_2 7 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 98
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 98 (accept_3_2 4 27 98 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 27 98 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 27 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 98 (Polychromatic418967fa.accept_20_2_7_18_1_4145 2 27 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 98 (accept_3_2 1 27 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 98))))))))))))))))))))))))))) (allB_succ 26 98 (allA_succ_of_accept 25 26
  98 (accept_3_2 25 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 98 2 12 13 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 98
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 98 2 11 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 26 98 (Polychromatic418967fa.accept_17_4_9_13_1_2020 21 26 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 98 2 10 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 98 (accept_3_2 19 26 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 26 98 2 9 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 26 98 (Polychromatic418967fa.accept_21_17_5_14_1_4144 17 26 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 98 2 8 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 98 (Polychromatic418967fa.accept_19_15_7_3_1_4143
  15 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 98 2 7 13 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 98 (accept_3_2 13 26
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 98 2 6 13 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 98
  (Polychromatic418967fa.accept_21_11_5_14_1_4142 11 26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 26 98 2 5 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 26 98 (Polychromatic418967fa.accept_21_9_5_14_1_1568 9 26 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 98 2 4 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 98 (accept_3_2 7 26 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 26 98 2 3 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 26 98 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 26 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 98 2 2 13 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 98 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3
  26 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 98 2 1 13 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 98 (accept_3_2 1 26
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 98)))))))))))))))))))))))))) (allB_succ 25 98 (allA_of_3_0 25
  25 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 98 (allA_succ_of_accept 23 24 98
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 24 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 98 2 11 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 24 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 98 2 10 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 98 (accept_3_2 19 24 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 24 98 2 9 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 24 98 (Polychromatic418967fa.accept_13_4_11_7_1_558 17 24 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 98 2 8 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 98 (Polychromatic418967fa.accept_21_15_3_14_1_4141
  15 24 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 98 2 7 12 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 98 (accept_3_2 13 24
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 98 2 6 12 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 98
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 24 98 2 5 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 24 98 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 24 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 98 2 4 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 98 (accept_3_2 7 24 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 24 98 2 3 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 24 98 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 98 2 2 12 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 98 2 1 12 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 98 (accept_3_2 1 24
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 98)))))))))))))))))))))))) (allB_succ 23 98
  (allA_succ_of_accept 22 23 98 (accept_3_2 22 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 98 (accept_3_2 19 23 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 98 (Polychromatic418967fa.accept_19_18_4_3_1_4140 18 23 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 98 (accept_3_2 16 23 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 98
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 98 (accept_3_2 13 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  98 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 23 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 23 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 98 (accept_3_2 10 23 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 23 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 98 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8
  23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 98 (accept_3_2 7 23 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 98 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 23
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 98
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 98 (accept_3_2 4 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 98
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 98 (accept_3_2 1 23 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 98))))))))))))))))))))))) (allB_succ 22 98 (allA_of_3_0 22 22 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 21 98 (allA_succ_of_accept 20 21 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 21 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 98 (accept_3_2 19 21 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 98 (Polychromatic418967fa.accept_12_6_9_2_1_311 18
  21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 98 (accept_3_2 16 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21
  98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 21 98 7 2 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 21 98 (accept_3_2 13 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21
  98 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 98 (accept_3_2 10 21 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 98 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 21 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 98
  (Polychromatic418967fa.accept_17_8_4_13_1_3014 8 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 21 98 7 1 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 21 98 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 98 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 98 (accept_3_2 4 21 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 98
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 98 (accept_3_2 1 21 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21
  98))))))))))))))))))))) (allB_succ 20 98 (allA_succ_of_accept 19 20 98 (accept_3_2 19 20 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 98 2 9 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 20 98 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 20 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 20 98 2 8 10 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 20 98
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 20 98 2 7 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 20 98 (accept_3_2 13 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 98
  2 6 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20
  98 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 20 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 20 98 2 5 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 20 98 (Polychromatic418967fa.accept_21_9_20_14_1_4139 9 20 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 98 2 4 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 98 (accept_3_2 7 20 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 20 98 2 3 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 20 98 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 20 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 20 98 2 2 10 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 20 98 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 20
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 98 2 1 10 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 98 (accept_3_2 1 20
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 98)))))))))))))))))))) (allB_succ 19 98 (allA_of_3_0 19 19 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 18 98 (allA_succ_of_accept 17 18 98
  (Polychromatic418967fa.accept_21_17_18_14_1_4138 17 18 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 98 2 8 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 18 98 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 18 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 18 98 2 7 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 98 (accept_3_2 13 18 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 18 98 2 6 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 18 98 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 18 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 98 2 5 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 18 98 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9
  18 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 98 2 4 9 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 98 (accept_3_2 7 18
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 98 2 3 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 98 (Polychromatic418967fa.accept_15_5_3_8_1_748 5 18
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 98 2 2 9 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 98
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 18 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 98 2 1 9 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 98 (accept_3_2 1 18 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  98)))))))))))))))))) (allB_succ 17 98 (allA_succ_of_accept 16 17 98 (accept_3_2 16 17 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 17 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 98 (Polychromatic418967fa.accept_19_14_17_3_1_4137
  14 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 98 (accept_3_2 13 17
  98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 98
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 17 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 98 (accept_3_2 10 17 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 17 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 98 (Polychromatic418967fa.accept_12_8_5_2_1_746 8
  17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 98 (accept_3_2 7 17 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 98 (Polychromatic418967fa.accept_13_6_4_7_1_2464 6
  17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 98
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 98 (accept_3_2 4 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 98 (Polychromatic418967fa.accept_18_2_17_8_1_1893 2 17 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 98 (accept_3_2 1 17 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 98))))))))))))))))) (allB_succ 16 98 (allA_of_3_0 16 16 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 15 98 (allA_succ_of_accept 14 15 98 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 15 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 98 (accept_3_2 13 15 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 12
  15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 98 (accept_3_2 10 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15
  98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 98 (Polychromatic418967fa.accept_13_8_2_7_1_2452 8 15 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 98 (accept_3_2 7 15 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 98 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 15 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 98 (accept_3_2 4 15 98
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 15
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 98
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 98 (accept_3_2 1 15 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  98))))))))))))))) (allB_succ 14 98 (allA_succ_of_accept 13 14 98 (accept_3_2 13 14 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 14 98 2 6 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 14 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 98 2 5 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 98 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 14
  98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 98 2 4 7 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 14 98 7 1 2 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 14 98 2 3 7 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 98
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 14 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 98 2 2 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 98 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 14 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 98 2 1 7 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 98 (accept_3_2 1 14 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 98)))))))))))))) (allB_succ 13 98 (allA_of_3_0 13 13 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 98 (allA_succ_of_accept 11 12 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 12 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 98 2 5 6 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 98
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 12 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 98 2 4 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 98 (accept_3_2 7 12 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 98 2
  3 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 98
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 98 2 2 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 12 98 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 12 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 98 2 1 6 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 98 (accept_3_2 1 12 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 98)))))))))))) (allB_succ 11 98 (allA_succ_of_accept 10 11 98 (accept_3_2 10 11 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 98
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 98 (accept_3_2 7 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 98
  (Polychromatic418967fa.accept_9_6_2_8_1_592 6 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 98 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 98 (accept_3_2 4 11 98 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 11 98 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 98 (Polychromatic418967fa.accept_19_2_11_3_1_4136 2 11 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 98 (accept_3_2 1 11 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 11 98))))))))))) (allB_succ 10 98 (allA_of_3_0 10 10 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 9 98 (allA_succ_of_accept 8 9 98 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 9 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 98 (accept_3_2 7 9 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 98 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 9 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 98
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 98 (accept_3_2 4 9 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 98
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 9 98 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 9 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 98 (accept_3_2 1 9 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 9 98))))))))) (allB_succ 8 98 (allA_succ_of_accept 7 8 98 (accept_3_2 7 8 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 98 2 3 4 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 8 98 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 8 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 98 2 2 4 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 98
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 8 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 8 98 2 1 4 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 8 98 (accept_3_2 1 8 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 98))))))))
  (allB_succ 7 98 (allA_of_3_0 7 7 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 98 (allA_succ_of_accept 5 6
  98 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 98 2 2 3 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 6 98 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 6 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 98 2 1 3 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 6 98 (accept_3_2 1 6 98 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  6 98)))))) (allB_succ 5 98 (allA_succ_of_accept 4 5 98 (accept_3_2 4 5 98 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 98 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 98 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 98 (accept_3_2 1 5 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 98))))) (allB_succ 4 98 (allA_of_3_0 4 4 98 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 98 (allA_succ_of_accept 2 3 98 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 3 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 98 (accept_3_2 1 3 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 3 98))) (allB_succ 2 98 (allA_succ_of_accept 1 2 98 (accept_3_2 1 2 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 2 98)) (allB_two
  98))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


