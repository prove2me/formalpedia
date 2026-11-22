-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch86
-- name    : Polychromatic418967fa_Branch86
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:13.253364+00:00
-- url     : https://prove2.me/theorems/88537952-c18d-4a67-8bde-3a47bdce97fd
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

def Polychromatic418967fa.branch_86 : allB 86 86 :=
  allB_succ' 2 85 86 (Eq.refl Bool.true) (allA_of_3_0 2 85 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3 84
  86 (Eq.refl Bool.true) (allA_succ_of_gcd 2 84 86 2 1 42 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 84 86 (accept_3_2 1 84 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 86))) (allB_succ' 4 83 86 (Eq.refl Bool.true) (allA_succ_of_accept 3 83 86
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 86 (Polychromatic418967fa.accept_16_2_3_6_1_3372 2 83 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 86 (accept_3_2 1 83 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 86)))) (allB_succ' 5 82 86 (Eq.refl Bool.true) (allA_of_3_0 5 82 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 81 86 (Eq.refl Bool.true) (allA_succ_of_accept 5 81 86
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 86 (accept_3_2 4 81 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 86 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 81 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 86 (accept_3_2 1 81 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 86)))))) (allB_succ' 7 80 86 (Eq.refl Bool.true) (allA_succ_of_gcd 6 80 86 2 3 40 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80 86
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 80 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 86 2 2 40 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 86 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 80 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 86 2 1 40 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 86 (accept_3_2 1 80 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 86))))))) (allB_succ' 8 79 86 (Eq.refl Bool.true) (allA_of_3_0 8 79 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 9 78 86 (Eq.refl Bool.true) (allA_succ_of_gcd 8 78 86 2 4 39 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 86 (accept_3_2 7 78 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 86 2 3 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 86 (Polychromatic418967fa.accept_19_5_2_10_1_3371 5 78 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 86 2 2 39 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 86
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 78 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 86 2 1 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 86 (accept_3_2 1 78 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 86)))))))))
  (allB_succ' 10 77 86 (Eq.refl Bool.true) (allA_succ_of_accept 9 77 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 86
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 86 (accept_3_2 7 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 86
  (Polychromatic418967fa.accept_15_6_2_11_1_325 6 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 86 (Polychromatic418967fa.accept_13_5_12_8_1_198 5 77 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 86 (accept_3_2 4 77 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 86 (Polychromatic418967fa.accept_22_2_11_20_1_3370
  2 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 86 (accept_3_2 1 77 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 86)))))))))) (allB_succ' 11 76 86 (Eq.refl Bool.true)
  (allA_of_3_0 11 76 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 75 86 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 86 (accept_3_2 10 75 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 86 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 75
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 86 (accept_3_2 7 75 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 86 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 75
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 86
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 86 (accept_3_2 4 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 86
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 86 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 75 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 86 (accept_3_2 1 75 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 75 86)))))))))))) (allB_succ' 13 74 86 (Eq.refl Bool.true) (allA_succ_of_gcd 12 74 86 2 6 37 43
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 86
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 74 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 86 2 5 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 86 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 74 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 86 2 4 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 86 (accept_3_2 7 74 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 86 2 3 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 86 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 74 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 86 2 2 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 86 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 74
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 86 2 1 37 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 86 (accept_3_2 1 74
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 86))))))))))))) (allB_succ' 14 73 86 (Eq.refl Bool.true)
  (allA_of_3_0 14 73 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 72 86 (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 72 86 2 7 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 86 (accept_3_2 13 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 86
  2 6 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72
  86 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 86 2 5 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 72 86 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 72 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 86 2 4 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 86 (accept_3_2 7 72 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 72 86 2 3 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 72 86 (Polychromatic418967fa.accept_17_5_4_1_1_3369 5 72 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 86 2 2 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 86 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3
  72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 86 2 1 36 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 86 (accept_3_2 1 72
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 86))))))))))))))) (allB_succ' 16 71 86 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 71 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 86 (Polychromatic418967fa.accept_13_1_6_8_1_208 14 71 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 86 (accept_3_2 13 71 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 86 (Polychromatic418967fa.accept_9_3_8_5_1_65 12
  71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 86
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 86 (accept_3_2 10 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71
  86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 71 86 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 71 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 86 (accept_3_2 7 71 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 71 86 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 71 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 86 (accept_3_2 4 71 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 86
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 86 (accept_3_2 1 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  86)))))))))))))))) (allB_succ' 17 70 86 (Eq.refl Bool.true) (allA_of_3_0 17 70 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 69 86 (Eq.refl Bool.true) (allA_succ_of_accept 17 69 86
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 86 (accept_3_2 16 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69
  86 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 86 (Polychromatic418967fa.accept_19_14_12_10_1_3368 14 69 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 86 (accept_3_2 13 69 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 86 (accept_3_2 10 69 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 86 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9
  69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 86
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 86 (accept_3_2 7 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 86
  (Polychromatic418967fa.accept_11_6_3_9_1_906 6 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 86 (accept_3_2 4 69 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 86 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 69
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 86 (accept_3_2 1 69 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 86)))))))))))))))))) (allB_succ' 19 68 86 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 68 86 2 9 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 68 86 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 86 2 8 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 86 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 68 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 86 2 7 34 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 86 (accept_3_2 13 68 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 86 2 6 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 86 (Polychromatic418967fa.accept_7_4_5_2_1_243 11
  68 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 86 2 5 34 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 86
  (Polychromatic418967fa.accept_13_9_3_8_1_573 9 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 86 2 4 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 86 (accept_3_2 7 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 86 2
  3 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68 86
  (Polychromatic418967fa.accept_12_5_8_2_1_309 5 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 86 2 2 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 86 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 68 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 86 2 1 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 86 (accept_3_2 1 68 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 86))))))))))))))))))) (allB_succ' 20 67 86 (Eq.refl Bool.true) (allA_of_3_0 20 67 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 66 86 (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 86 2 10 33 43
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 86
  (accept_3_2 19 66 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 86 2 9 33 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 86
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 66 86 2 8 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 66 86 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 66 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 86 2 7 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 86 (accept_3_2 13 66 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 66 86 2 6 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 66 86 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 66 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 86 2 5 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 86 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9
  66 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 86 2 4 33 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 86 (accept_3_2 7 66
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 86 2 3 33 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 86
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 86 2 2 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 66 86 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 66 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 86 2 1 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 86 (accept_3_2 1 66 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 86))))))))))))))))))))) (allB_succ' 22 65 86 (Eq.refl Bool.true) (allA_succ_of_accept 21 65
  86 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 65 86 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 65 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 86 (accept_3_2 19 65 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 65 86 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 65 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 86 (Polychromatic418967fa.accept_9_8_2_5_1_237 17
  65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 86 (accept_3_2 16 65 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 86
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 86 (accept_3_2 13 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65
  86 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 65 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 86 (accept_3_2 10 65 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 65 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 86 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 86 (accept_3_2 7 65 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 86 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 65
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 86
  (Polychromatic418967fa.accept_16_5_1_6_1_3367 5 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 86 (accept_3_2 4 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 86 (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 65 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 86 (accept_3_2 1 65 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 86)))))))))))))))))))))) (allB_succ' 23 64 86 (Eq.refl Bool.true) (allA_of_3_0 23 64 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 63 86 (Eq.refl Bool.true) (allA_succ_of_accept 23 63 86
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 86 (accept_3_2 22 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63
  86 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 86 (Polychromatic418967fa.accept_19_1_6_10_1_3366 20 63 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 86 (accept_3_2 19 63 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 86 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 86 (accept_3_2 16 63 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 86 (Polychromatic418967fa.accept_17_15_12_1_1_3365
  15 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 86
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 86 (accept_3_2 13 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63
  86 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 86 (accept_3_2 10 63 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 86
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 86 (accept_3_2 7 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 86
  (Polychromatic418967fa.accept_12_6_3_2_1_743 6 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 86 (accept_3_2 4 63 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 63 86 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 63 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 86 (Polychromatic418967fa.accept_19_2_6_10_1_3364 2 63 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 86 (accept_3_2 1 63 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 86)))))))))))))))))))))))) (allB_succ' 25 62 86 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 62 86 2 12 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 62 86 (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 62 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 86 2 11 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 86 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 62 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 86 2 10 31 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 86 (accept_3_2 19 62 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 86 2 9 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 62 86 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 62
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 86 2 8 31 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 86
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 62 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 86 2 7 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 86 (accept_3_2 13 62 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 86
  2 6 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62
  86 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 62 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 86 2 5 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 86 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 62 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 86 2 4 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 86 (accept_3_2 7 62 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 86 2 3 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 86 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 62 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 86 2 2 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 86 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 62
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 86 2 1 31 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 86 (accept_3_2 1 62
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 86))))))))))))))))))))))))) (allB_succ' 26 61 86 (Eq.refl
  Bool.true) (allA_of_3_0 26 61 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 60 86 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 60 86 2 13 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 60 86 (accept_3_2 25 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 86
  2 12 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60
  86 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 86 2 11 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 60 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 86 2 10 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 86 (accept_3_2 19 60 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 60 86 2 9 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 60 86 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 86 2 8 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 86 (Polychromatic418967fa.accept_17_15_9_1_1_3363
  15 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 86 2 7 30 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 86 (accept_3_2 13 60
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 86 2 6 30 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 86
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 86 2 5 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 60 86 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 60 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 86 2 4 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 86 (accept_3_2 7 60 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 60 86 2 3 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 60 86 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 86 2 2 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 86 2 1 30 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 86 (accept_3_2 1 60
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 86))))))))))))))))))))))))))) (allB_succ' 28 59 86 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 59 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 86 (Polychromatic418967fa.accept_7_5_3_2_1_249 26
  59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 86 (accept_3_2 25 59 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 86 (Polychromatic418967fa.accept_11_2_4_9_1_484 24
  59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 86
  (Polychromatic418967fa.accept_10_3_9_6_1_94 23 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 86 (accept_3_2 22 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59
  86 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 59 86 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 86 (accept_3_2 19 59 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 59 86 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 59 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 86 (accept_3_2 16 59 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 86
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 86 (accept_3_2 13 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59
  86 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 59 86 (Polychromatic418967fa.accept_17_11_8_1_1_3362 11 59 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 86 (accept_3_2 10 59 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 59 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 86 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 86 (accept_3_2 7 59 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 86 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 86
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 86 (accept_3_2 4 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 86
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 86 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 59 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 86 (accept_3_2 1 59 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 86)))))))))))))))))))))))))))) (allB_succ' 29 58 86 (Eq.refl Bool.true) (allA_of_3_0 29 58 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 57 86 (Eq.refl Bool.true) (allA_succ_of_accept 29 57 86
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 86 (accept_3_2 28 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57
  86 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 86 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 86 (accept_3_2 25 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 86 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 86 (accept_3_2 22 57 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 86 (Polychromatic418967fa.accept_10_1_7_6_1_91 21
  57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 86
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 86 (accept_3_2 19 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57
  86 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 86 (accept_3_2 16 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 86 (Polychromatic418967fa.accept_13_1_5_8_1_207 14
  57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 86 (accept_3_2 13 57 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 86 (Polychromatic418967fa.accept_13_12_5_8_1_1101
  12 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 86 (accept_3_2 10 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57
  86 (Polychromatic418967fa.accept_18_9_3_14_1_3361 9 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 86 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 86 (accept_3_2 7 57 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 57 86 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 57 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 86 (accept_3_2 4 57 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 86
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 86 (accept_3_2 1 57 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  86)))))))))))))))))))))))))))))) (allB_succ' 31 56 86 (Eq.refl Bool.true) (allA_succ_of_gcd 30 56 86 2 15 28 43
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 86
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 86 2 14 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 86 (Polychromatic418967fa.accept_19_8_18_10_1_3360 27 56 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 86 2 13 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 86 (accept_3_2 25 56 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 56 86 2 12 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 56 86 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 56 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 86 2 11 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 86 (Polychromatic418967fa.accept_9_3_2_5_1_234 21
  56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 86 2 10 28 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 86 (accept_3_2 19 56
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 86 2 9 28 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 86
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 56 86 2 8 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 56 86 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 56 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 86 2 7 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 86 (accept_3_2 13 56 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 56 86 2 6 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 56 86 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 56 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 86 2 5 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 86 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9
  56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 86 2 4 28 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 86 (accept_3_2 7 56
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 86 2 3 28 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56 86
  (Polychromatic418967fa.accept_12_5_8_2_1_309 5 56 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 86 2 2 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 86 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 56 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 86 2 1 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 86 (accept_3_2 1 56 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 86))))))))))))))))))))))))))))))) (allB_succ' 32 55 86 (Eq.refl Bool.true) (allA_of_3_0 32 55
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 54 86 (Eq.refl Bool.true) (allA_succ_of_gcd 32 54 86 2 16
  27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 86
  (accept_3_2 31 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 86 2 15 27 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 86
  (Polychromatic418967fa.accept_20_9_14_6_1_320 29 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 86 2 14 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 54 86 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 54 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 86 2 13 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 86 (accept_3_2 25 54 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 54 86 2 12 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 86 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 54 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 86 2 11 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 86 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21
  54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 86 2 10 27 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 86 (accept_3_2 19 54
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 86 2 9 27 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 86
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 54 86 2 8 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 54 86 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 54 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 86 2 7 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 86 (accept_3_2 13 54 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 54 86 2 6 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 54 86 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 86 2 5 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 86 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9
  54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 86 2 4 27 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 86 (accept_3_2 7 54
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 86 2 3 27 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 86
  (Polychromatic418967fa.accept_10_5_4_6_1_319 5 54 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 54 86 2 2 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 54 86 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 86 2 1 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 86 (accept_3_2 1 54 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 54 86))))))))))))))))))))))))))))))))) (allB_succ' 34 53 86 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 53 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 86 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 53 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 86 (accept_3_2 31 53 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 86 (Polychromatic418967fa.accept_9_3_8_5_1_65 30
  53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 86
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 86 (accept_3_2 28 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53
  86 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 53 86 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 86 (accept_3_2 25 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 53 86 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 86 (accept_3_2 22 53 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 86
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 86 (accept_3_2 19 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53
  86 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 53 86 (Polychromatic418967fa.accept_10_7_3_6_1_644 17 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 86 (accept_3_2 16 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 53 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 86
  (Polychromatic418967fa.accept_19_14_15_10_1_3359 14 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 86 (accept_3_2 13 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53
  86 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 53 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 86 (accept_3_2 10 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 53 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 86 (Polychromatic418967fa.accept_10_8_3_6_1_685 8
  53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 86 (accept_3_2 7 53 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 86 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 53
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 86
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 86 (accept_3_2 4 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 86 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 86 (accept_3_2 1 53 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 86)))))))))))))))))))))))))))))))))) (allB_succ' 35 52 86 (Eq.refl Bool.true) (allA_of_3_0 35
  52 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 51 86 (Eq.refl Bool.true) (allA_succ_of_accept 35 51 86
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 86 (accept_3_2 34 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51
  86 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 86 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 86 (accept_3_2 31 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 86 (accept_3_2 28 51 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 86 (Polychromatic418967fa.accept_10_7_1_6_1_673 27
  51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 86
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 86 (accept_3_2 25 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51
  86 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 86 (accept_3_2 22 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 86 (Polychromatic418967fa.accept_9_2_6_5_1_227 20
  51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 86 (accept_3_2 19 51 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 86 (Polychromatic418967fa.accept_12_6_3_2_1_743 18
  51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 86
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 86 (accept_3_2 16 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51
  86 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 86 (Polychromatic418967fa.accept_13_1_12_8_1_1818 14 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 86 (accept_3_2 13 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 86 (accept_3_2 10 51 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 86
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 86 (accept_3_2 7 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 86
  (Polychromatic418967fa.accept_12_6_3_2_1_743 6 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 86 (accept_3_2 4 51 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 86 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 51 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 86 (accept_3_2 1 51 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 86)))))))))))))))))))))))))))))))))))) (allB_succ' 37 50 86 (Eq.refl
  Bool.true) (allA_succ_of_gcd 36 50 86 2 18 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 86 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 50 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 86 2 17 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 86 (Polychromatic418967fa.accept_16_1_2_6_1_2295 33
  50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 86 2 16 25 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 86 (accept_3_2 31 50
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 86 2 15 25 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 86
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 29 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 86 2 14 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 86 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 50 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 86 2 13 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 86 (accept_3_2 25 50 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 50 86 2 12 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 86 (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 50 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 86 2 11 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 86 (Polychromatic418967fa.accept_15_6_5_11_1_2378
  21 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 86 2 10 25 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 86 (accept_3_2 19 50
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 86 2 9 25 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 50 86
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 50 86 2 8 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 50 86 (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 50 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 86 2 7 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 86 (accept_3_2 13 50 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 50 86 2 6 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 50 86 (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 50 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 86 2 5 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 86 (Polychromatic418967fa.accept_13_9_11_8_1_195 9
  50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 86 2 4 25 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 86 (accept_3_2 7 50
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 86 2 3 25 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50 86
  (Polychromatic418967fa.accept_17_5_16_1_1_3358 5 50 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 50 86 2 2 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 50 86 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 50 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 86 2 1 25 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 86 (accept_3_2 1 50 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 86))))))))))))))))))))))))))))))))))))) (allB_succ' 38 49 86 (Eq.refl Bool.true) (allA_of_3_0
  38 49 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 48 86 (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 86
  2 19 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48
  86 (accept_3_2 37 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 86 2 18 24 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 86
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 86 2 17 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 48 86 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 86 2 16 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 86 (accept_3_2 31 48 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 48 86 2 15 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 48 86 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 86 2 14 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 86 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27
  48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 86 2 13 24 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 86 (accept_3_2 25 48
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 86 2 12 24 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 86
  (Polychromatic418967fa.accept_10_3_8_6_1_326 23 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 86 2 11 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 48 86 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 48 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 86 2 10 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 86 (accept_3_2 19 48 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 48 86 2 9 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 48 86 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 86 2 8 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 86 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 86 2 7 24 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 86 (accept_3_2 13 48
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 86 2 6 24 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 86
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 86 2 5 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 48 86 (Polychromatic418967fa.accept_21_9_6_2_1_3357 9 48 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 86 2 4 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 86 (accept_3_2 7 48 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 48 86 2 3 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 48 86 (Polychromatic418967fa.accept_25_5_23_11_1_684 5 48 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 86 2 2 24 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 86 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 86 2 1 24 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 86 (accept_3_2 1 48
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 86))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 47
  86 (Eq.refl Bool.true) (allA_succ_of_accept 39 47 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 86
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 86 (accept_3_2 37 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47
  86 (Polychromatic418967fa.accept_15_6_2_11_1_325 36 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 47 86 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 86 (accept_3_2 34 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 47 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 86 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 86 (accept_3_2 31 47 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 86 (Polychromatic418967fa.accept_9_3_2_5_1_234 30
  47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 86
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 86 (accept_3_2 28 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47
  86 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 86 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 86 (accept_3_2 25 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 86 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 86 (Polychromatic418967fa.accept_10_3_7_6_1_659 23
  47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 86 (accept_3_2 22 47 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 86
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 86 (accept_3_2 19 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47
  86 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 47 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 86 (accept_3_2 16 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 47 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 86 (Polychromatic418967fa.accept_17_14_13_1_1_3356
  14 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 86 (accept_3_2 13 47
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 86 (Polychromatic418967fa.accept_9_3_2_5_1_234
  12 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 86
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 86 (accept_3_2 10 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47
  86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 86 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 86 (accept_3_2 7 47 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 86 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 47 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 86 (accept_3_2 4 47 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 86
  (Polychromatic418967fa.accept_17_2_13_1_1_3355 2 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 86 (accept_3_2 1 47 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  86)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 46 86 (Eq.refl Bool.true) (allA_of_3_0 41 46 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 45 86 (Eq.refl Bool.true) (allA_succ_of_accept 41 45 86
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 86 (accept_3_2 40 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45
  86 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 86 (Polychromatic418967fa.accept_21_17_3_2_1_2111 38 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 86 (accept_3_2 37 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 86 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 86 (accept_3_2 34 45 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 86 (Polychromatic418967fa.accept_7_5_3_2_1_249 33
  45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 86
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 86 (accept_3_2 31 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45
  86 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 86 (accept_3_2 28 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 86 (Polychromatic418967fa.accept_7_5_3_2_1_249 26
  45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 86 (accept_3_2 25 45 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 86 (Polychromatic418967fa.accept_10_4_5_6_1_651 24
  45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 86 (accept_3_2 22 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45
  86 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 86 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 86 (accept_3_2 19 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 86 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 45 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 17
  45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 86 (accept_3_2 16 45 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 86
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 86 (accept_3_2 13 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45
  86 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 86 (accept_3_2 10 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 86 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 45 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 86 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 45
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 86 (accept_3_2 7 45 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 86 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 45
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 86
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 86 (accept_3_2 4 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 86 (Polychromatic418967fa.accept_13_2_6_8_1_1092 2 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 86 (accept_3_2 1 45 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 45 86)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 44 86 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 44 86 2 21 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 86 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 44 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 86 2 20 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 86 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 44 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 86 2 19 22 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 86 (accept_3_2 37 44 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 86 2 18 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 86 (Polychromatic418967fa.accept_10_5_4_6_1_319 35
  44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 86 2 17 22 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 86
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 86 2 16 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 86 (accept_3_2 31 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 86
  2 15 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44
  86 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 44 86 2 14 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 44 86 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 44 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 86 2 13 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 86 (accept_3_2 25 44 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 44 86 2 12 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 44 86 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 44 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 86 2 11 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 86 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 44
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 86 2 10 22 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 86 (accept_3_2 19 44
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 86 2 9 22 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 86
  (Polychromatic418967fa.accept_12_5_8_2_1_309 17 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 44 86 2 8 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 44 86 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 44 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 86 2 7 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 86 (accept_3_2 13 44 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 44 86 2 6 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 44 86 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 86 2 5 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 86 (Polychromatic418967fa.accept_17_9_10_1_1_3345 9
  44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 86 2 4 22 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 86 (accept_3_2 7 44
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 86 2 3 22 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44 86
  (Polychromatic418967fa.accept_10_5_4_6_1_319 5 44 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 86 2 2 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 86 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 44 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 86 2 1 22 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 86 (accept_3_2 1 44 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 86))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 86 (allA_of_3_0 43 43 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 42 86 (allA_succ_of_accept 41 42 86
  (Polychromatic418967fa.accept_10_1_2_6_1_638 41 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 86 2 20 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 86 2 19 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 86 (accept_3_2 37 42 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 42 86 2 18 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 42 86 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 42 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 86 2 17 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 86 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33
  42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 86 2 16 21 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 86 (accept_3_2 31 42
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 86 2 15 21 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 86
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 86 2 14 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 42 86 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 42 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 86 2 13 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 86 (accept_3_2 25 42 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 42 86 2 12 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 86 (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 42 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 86 2 11 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 86 2 10 21 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 86 (accept_3_2 19 42
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 86 2 9 21 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 86
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 86 2 8 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 42 86 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 42 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 86 2 7 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 86 (accept_3_2 13 42 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 42 86 2 6 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 42 86 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 86 2 5 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 86 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9
  42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 86 2 4 21 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 86 (accept_3_2 7 42
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 86 2 3 21 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 86
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 5 42 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 86 2 2 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 42 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 86 2 1 21 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 86 (accept_3_2 1 42 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 86)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 86 (allA_succ_of_accept 40 41 86
  (accept_3_2 40 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 86 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 86 (accept_3_2 37 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 86 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 86 (accept_3_2 34 41 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 86
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 86 (accept_3_2 31 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  86 (Polychromatic418967fa.accept_19_11_3_10_1_3354 30 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 86 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 86 (accept_3_2 28 41 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 86
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 26 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 86 (accept_3_2 25 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41
  86 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 41 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 86 (accept_3_2 22 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 41 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 86 (Polychromatic418967fa.accept_12_8_5_2_1_746 20
  41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 86 (accept_3_2 19 41 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 86 (Polychromatic418967fa.accept_7_4_6_2_1_451 18
  41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 86
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 86 (accept_3_2 16 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41
  86 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 41 86 (Polychromatic418967fa.accept_20_14_1_6_1_3352 14 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 86 (accept_3_2 13 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 41 86 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 41 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 86 (accept_3_2 10 41 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 86
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 86 (accept_3_2 7 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 86
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 86 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 86 (accept_3_2 4 41 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 86 (Polychromatic418967fa.accept_10_2_1_6_1_634 2
  41 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 86 (accept_3_2 1 41 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 86))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 86
  (allA_of_3_0 40 40 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 86 (allA_succ_of_accept 38 39 86
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 86 (accept_3_2 37 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39
  86 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 86 (accept_3_2 34 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 86 (Polychromatic418967fa.accept_15_2_9_11_1_1551
  32 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 86 (accept_3_2 31 39
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 86 (Polychromatic418967fa.accept_12_6_3_2_1_743
  30 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 86
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 86 (accept_3_2 28 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39
  86 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 86 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 86 (accept_3_2 25 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 86 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 23
  39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 86 (accept_3_2 22 39 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 86
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 86 (accept_3_2 19 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39
  86 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 86 (accept_3_2 16 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 86 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 86 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  14 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 86 (accept_3_2 13 39
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 86 (Polychromatic418967fa.accept_7_5_4_2_1_235
  12 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 86
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 86 (accept_3_2 10 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39
  86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 86 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 86 (accept_3_2 7 39 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 39 86 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 86 (accept_3_2 4 39 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 86 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 39
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 86
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 86 (accept_3_2 1 39 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  86))))))))))))))))))))))))))))))))))))))) (allB_succ 38 86 (allA_succ_of_accept 37 38 86 (accept_3_2 37 38 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38 86 2 18 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 38 86 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 38 86 2 17 19 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 38 86
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 38 86 2 16 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 38 86 (accept_3_2 31 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 86
  2 15 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38
  86 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 86 2 14 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 86 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 38 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 86 2 13 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 86 (accept_3_2 25 38 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 38 86 2 12 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 38 86 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 38 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 86 2 11 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 86 (Polychromatic418967fa.accept_9_3_2_5_1_234 21
  38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 86 2 10 19 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 86 (accept_3_2 19 38
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38 86 2 9 19 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 38 86
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 38 86 2 8 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 38 86 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 38 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 86 2 7 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 86 (accept_3_2 13 38 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 38 86 2 6 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 38 86 (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 38 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 86 2 5 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 86 (Polychromatic418967fa.accept_13_9_12_8_1_570 9
  38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 86 2 4 19 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 86 (accept_3_2 7 38
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 86 2 3 19 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38 86
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 38 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 86 2 2 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 86 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 38 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 86 2 1 19 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 86 (accept_3_2 1 38 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 86)))))))))))))))))))))))))))))))))))))) (allB_succ 37 86 (allA_of_3_0 37 37 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 86 (allA_succ_of_accept 35 36 86
  (Polychromatic418967fa.accept_15_5_6_11_1_854 35 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 86 2 17 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 86 (Polychromatic418967fa.accept_13_7_10_8_1_567 33 36 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 86 2 16 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 86 (accept_3_2 31 36 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 36 86 2 15 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 36 86 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 36 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 86 2 14 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 86 (Polychromatic418967fa.accept_7_6_1_2_1_230 27
  36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 86 2 13 18 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 86 (accept_3_2 25 36
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 86 2 12 18 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 86
  (Polychromatic418967fa.accept_17_6_2_1_1_3350 23 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 36 86 2 11 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 36 86 (Polychromatic418967fa.accept_16_5_4_6_1_3349 21 36 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 86 2 10 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 86 (accept_3_2 19 36 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 36 86 2 9 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 36 86 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 86 2 8 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 86 (Polychromatic418967fa.accept_13_2_10_8_1_1126
  15 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 86 2 7 18 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 86 (accept_3_2 13 36
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 86 2 6 18 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 86
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 36 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 86 2 5 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 36 86 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 36 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 86 2 4 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 86 (accept_3_2 7 36 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 36 86 2 3 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 36 86 (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 36 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 86 2 2 18 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 86 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 86 2 1 18 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 86 (accept_3_2 1 36
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 86)))))))))))))))))))))))))))))))))))) (allB_succ 35 86
  (allA_succ_of_accept 34 35 86 (accept_3_2 34 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35
  86 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 86 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 86 (accept_3_2 31 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 86 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 35 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 86 (accept_3_2 28 35 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 27
  35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 86
  (Polychromatic418967fa.accept_11_4_2_9_1_496 26 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 86 (accept_3_2 25 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35
  86 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 35 86 (Polychromatic418967fa.accept_14_9_7_2_1_2483 23 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 86 (accept_3_2 22 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 35 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 86 (Polychromatic418967fa.accept_9_2_8_5_1_228 20
  35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 86 (accept_3_2 19 35 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 86 (Polychromatic418967fa.accept_11_7_2_9_1_480 18
  35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 86
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 86 (accept_3_2 16 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35
  86 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 86 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 86 (accept_3_2 13 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 86 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 86 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 86 (accept_3_2 10 35 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 86
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 86 (accept_3_2 7 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 86
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 86 (accept_3_2 4 35 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 35 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 86 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 35 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 86 (accept_3_2 1 35 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 35 86))))))))))))))))))))))))))))))))))) (allB_succ 34 86 (allA_of_3_0 34 34
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 86 (allA_succ_of_accept 32 33 86
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 86 (accept_3_2 31 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33
  86 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 86 (accept_3_2 28 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 86 (Polychromatic418967fa.accept_9_8_6_5_1_513 26
  33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 86 (accept_3_2 25 33 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 86 (Polychromatic418967fa.accept_7_3_5_2_1_17 24
  33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 86 (accept_3_2 22 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33
  86 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 86 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 86 (accept_3_2 19 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 86 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 33 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 17
  33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 86 (accept_3_2 16 33 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 86
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 86 (accept_3_2 13 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33
  86 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 86 (accept_3_2 10 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 86 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 33 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 86 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 33
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 86 (accept_3_2 7 33 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 86 (Polychromatic418967fa.accept_12_6_9_2_1_311 6
  33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 86
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 86 (accept_3_2 4 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 86 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 86 (accept_3_2 1 33 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 86))))))))))))))))))))))))))))))))) (allB_succ 32 86 (allA_succ_of_accept 31 32 86
  (accept_3_2 31 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 86 2 15 16 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 86
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 86 2 14 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 86 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 32 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 86 2 13 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 86 (accept_3_2 25 32 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 32 86 2 12 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 32 86 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 32 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 86 2 11 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 86 (Polychromatic418967fa.accept_10_1_2_6_1_638 21
  32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 86 2 10 16 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 86 (accept_3_2 19 32
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 86 2 9 16 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32 86
  (Polychromatic418967fa.accept_12_5_8_2_1_309 17 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 32 86 2 8 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 32 86 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 32 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 86 2 7 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 86 (accept_3_2 13 32 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 32 86 2 6 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 32 86 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 32 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 86 2 5 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 86 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 32
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 86 2 4 16 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 86 (accept_3_2 7 32
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 86 2 3 16 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 86
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 86 2 2 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 86 (Polychromatic418967fa.accept_17_3_15_1_1_3348 3 32 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 86 2 1 16 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 86 (accept_3_2 1 32 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 86)))))))))))))))))))))))))))))))) (allB_succ 31 86 (allA_of_3_0 31 31 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 30 86 (allA_succ_of_accept 29 30 86 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 30
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 86 2 14 15 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 86
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 30 86 2 13 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 86 (accept_3_2 25 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 86
  2 12 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30
  86 (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 30 86 2 11 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 30 86 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 30 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 86 2 10 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 86 (accept_3_2 19 30 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 86 2 9 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 30 86 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 30 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 86 2 8 15 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 86
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 30 86 2 7 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 30 86 (accept_3_2 13 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 86
  2 6 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30
  86 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 30 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 86 2 5 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 86 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 30 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 86 2 4 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 86 (accept_3_2 7 30 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 86 2 3 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 30 86 (Polychromatic418967fa.accept_19_5_11_10_1_3347 5 30 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 86 2 2 15 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 86 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 30
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 86 2 1 15 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 86 (accept_3_2 1 30
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 86)))))))))))))))))))))))))))))) (allB_succ 29 86
  (allA_succ_of_accept 28 29 86 (accept_3_2 28 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29
  86 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 86 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 29 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 86 (accept_3_2 25 29 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 86 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 86 (accept_3_2 22 29 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 86
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 86 (accept_3_2 19 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29
  86 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 29 86 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 86 (accept_3_2 16 29 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 29 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 86 (Polychromatic418967fa.accept_20_14_9_6_1_3346
  14 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 86 (accept_3_2 13 29
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 86 (Polychromatic418967fa.accept_9_3_2_5_1_234
  12 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 86 (accept_3_2 10 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29
  86 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 86 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 86 (accept_3_2 7 29 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 86 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 29 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 86 (Polychromatic418967fa.accept_10_5_9_6_1_697 5
  29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 86 (accept_3_2 4 29 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 86
  (Polychromatic418967fa.accept_11_2_7_9_1_890 2 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 86 (accept_3_2 1 29 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  86))))))))))))))))))))))))))))) (allB_succ 28 86 (allA_of_3_0 28 28 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 27 86 (allA_succ_of_accept 26 27 86 (Polychromatic418967fa.accept_17_9_10_1_1_3345 26 27 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 86 (accept_3_2 25 27 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 86 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 86
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 86 (accept_3_2 22 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27
  86 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 86 (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 27 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 86 (accept_3_2 19 27 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 86 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 86 (accept_3_2 16 27 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 86 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 86
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 86 (accept_3_2 13 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27
  86 (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 86 (accept_3_2 10 27 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 86
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 86 (accept_3_2 7 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 86
  (Polychromatic418967fa.accept_12_6_3_2_1_743 6 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 86 (accept_3_2 4 27 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 27 86 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 86 (Polychromatic418967fa.accept_16_2_11_6_1_737 2 27 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 86 (accept_3_2 1 27 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 86))))))))))))))))))))))))))) (allB_succ 26 86 (allA_succ_of_accept 25 26
  86 (accept_3_2 25 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 86 2 12 13 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 86
  (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 86 2 11 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 26 86 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 26 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 86 2 10 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 86 (accept_3_2 19 26 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 26 86 2 9 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 26 86 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 26 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 86 2 8 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 86 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 86 2 7 13 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 86 (accept_3_2 13 26
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 86 2 6 13 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 86
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 26 86 2 5 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 26 86 (Polychromatic418967fa.accept_19_9_7_10_1_1170 9 26 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 86 2 4 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 86 (accept_3_2 7 26 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 26 86 2 3 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 26 86 (Polychromatic418967fa.accept_18_5_8_14_1_1282 5 26 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 86 2 2 13 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 86 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 26
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 86 2 1 13 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 86 (accept_3_2 1 26
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 86)))))))))))))))))))))))))) (allB_succ 25 86 (allA_of_3_0 25
  25 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 86 (allA_succ_of_accept 23 24 86
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 24 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 86 2 11 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 24 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 86 2 10 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 86 (accept_3_2 19 24 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 24 86 2 9 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 24 86 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 86 2 8 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 86 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 86 2 7 12 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 86 (accept_3_2 13 24
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 86 2 6 12 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 86
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 24 86 2 5 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 24 86 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 24 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 86 2 4 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 86 (accept_3_2 7 24 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 24 86 2 3 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 24 86 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 86 2 2 12 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 86 2 1 12 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 86 (accept_3_2 1 24
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 86)))))))))))))))))))))))) (allB_succ 23 86
  (allA_succ_of_accept 22 23 86 (accept_3_2 22 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23
  86 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 86 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 23 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 86 (accept_3_2 19 23 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 86 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 23 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 86 (accept_3_2 16 23 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 86
  (Polychromatic418967fa.accept_19_14_4_10_1_3344 14 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 86 (accept_3_2 13 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  86 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 86 (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 23 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 86 (accept_3_2 10 23 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 86
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 86 (accept_3_2 7 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 86
  (Polychromatic418967fa.accept_19_6_4_10_1_3342 6 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 86 (accept_3_2 4 23 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 23 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 86 (Polychromatic418967fa.accept_13_2_10_8_1_1126 2 23 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 86 (accept_3_2 1 23 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 23 86))))))))))))))))))))))) (allB_succ 22 86 (allA_of_3_0 22 22 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 21 86 (allA_succ_of_accept 20 21 86
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 86 (accept_3_2 19 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21
  86 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 86 (accept_3_2 16 21 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 86 (Polychromatic418967fa.accept_17_14_4_1_1_3341
  14 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 86 (accept_3_2 13 21
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 86 (Polychromatic418967fa.accept_10_2_1_6_1_634
  12 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 86 (accept_3_2 10 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21
  86 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 86 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 21 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 86 (accept_3_2 7 21 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 21 86 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 86 (accept_3_2 4 21 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 86
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 86 (accept_3_2 1 21 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21
  86))))))))))))))))))))) (allB_succ 20 86 (allA_succ_of_accept 19 20 86 (accept_3_2 19 20 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 86 2 9 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 20 86 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 20 86 2 8 10 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 20 86
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 20 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 20 86 2 7 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 20 86 (accept_3_2 13 20 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 86
  2 6 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20
  86 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 86 2 5 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 86 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 20 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 86 2 4 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 86 (accept_3_2 7 20 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 20 86 2 3 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 20 86 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 20 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 20 86 2 2 10 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 20 86 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 20
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 86 2 1 10 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 86 (accept_3_2 1 20
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 86)))))))))))))))))))) (allB_succ 19 86 (allA_of_3_0 19 19 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 18 86 (allA_succ_of_accept 17 18 86
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 18 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 86 2 8 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 18 86 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 18 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 18 86 2 7 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 86 (accept_3_2 13 18 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 18 86 2 6 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 18 86 (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 18 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 86 2 5 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 18 86 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9
  18 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 86 2 4 9 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 86 (accept_3_2 7 18
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 86 2 3 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 86 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 86 2 2 9 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 86
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 18 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 86 2 1 9 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 86 (accept_3_2 1 18 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  86)))))))))))))))))) (allB_succ 17 86 (allA_succ_of_accept 16 17 86 (accept_3_2 16 17 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 17 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 86 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  14 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 86 (accept_3_2 13 17
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 86 (Polychromatic418967fa.accept_7_5_3_2_1_249
  12 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 86
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 86 (accept_3_2 10 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17
  86 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 86 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 86 (accept_3_2 7 17 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 86 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 86 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 86 (accept_3_2 4 17 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 86
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 86 (accept_3_2 1 17 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  86))))))))))))))))) (allB_succ 16 86 (allA_of_3_0 16 16 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 86
  (allA_succ_of_accept 14 15 86 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 15 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 86 (accept_3_2 13 15 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 86 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 15 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 86 (accept_3_2 10 15 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 86
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 86 (accept_3_2 7 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 86
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 86 (accept_3_2 4 15 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 86 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 86 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 15 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 86 (accept_3_2 1 15 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 86))))))))))))))) (allB_succ 14 86 (allA_succ_of_accept 13 14 86
  (accept_3_2 13 14 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 86 2 6 7 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 86
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 14 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 86 2 5 7 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 86 (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 14 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 86 2 4 7 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 86 (accept_3_2 7 14 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 86 2 3 7 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 86 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 14 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 86 2 2 7 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 86 (Polychromatic418967fa.accept_15_3_14_11_1_1579 3
  14 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 86 2 1 7 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 86 (accept_3_2 1 14
  86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 86)))))))))))))) (allB_succ 13 86 (allA_of_3_0 13 13 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 86 (allA_succ_of_accept 11 12 86
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 86 2 5 6 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 86 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 12 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 86 2 4 6 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 86 (accept_3_2 7 12 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 86 2 3 6 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 86 (Polychromatic418967fa.accept_13_5_12_8_1_198 5 12 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 86 2 2 6 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 86 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 86 2 1 6 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 86 (accept_3_2 1 12 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 86)))))))))))) (allB_succ 11 86 (allA_succ_of_accept 10 11 86 (accept_3_2
  10 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 86
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 86 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 86 (accept_3_2 7 11 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 86 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 86 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 86 (accept_3_2 4 11 86
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 86 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 86
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 86 (accept_3_2 1 11 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 86)))))))))))
  (allB_succ 10 86 (allA_of_3_0 10 10 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 86 (allA_succ_of_accept 8
  9 86 (Polychromatic418967fa.accept_17_8_9_1_1_3340 8 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 86 (accept_3_2 7 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 86
  (Polychromatic418967fa.accept_12_6_9_2_1_311 6 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 86 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 86 (accept_3_2 4 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 86 (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 9 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 86 (accept_3_2 1 9 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 9 86))))))))) (allB_succ 8 86 (allA_succ_of_accept 7 8 86 (accept_3_2 7 8 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 86 2 3 4 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 86 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 8 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 86 2 2 4 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 86
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 8 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 8 86 2 1 4 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 8 86 (accept_3_2 1 8 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 86))))))))
  (allB_succ 7 86 (allA_of_3_0 7 7 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 86 (allA_succ_of_accept 5 6
  86 (Polychromatic418967fa.accept_15_5_6_11_1_854 5 6 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 86 2 2 3 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 6 86 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 86 2 1 3 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 6 86 (accept_3_2 1 6 86 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  6 86)))))) (allB_succ 5 86 (allA_succ_of_accept 4 5 86 (accept_3_2 4 5 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 86 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 86 (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 5 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 86 (accept_3_2 1 5 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 5 86))))) (allB_succ 4 86 (allA_of_3_0 4 4 86 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 86 (allA_succ_of_accept 2 3 86 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 3 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 86 (accept_3_2 1 3 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 3 86))) (allB_succ 2 86 (allA_succ_of_accept 1 2 86 (accept_3_2 1 2 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 2 86)) (allB_two
  86))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


