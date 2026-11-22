-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch90
-- name    : Polychromatic418967fa_Branch90
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:27.544297+00:00
-- url     : https://prove2.me/theorems/6c3bdc03-f8fa-47f4-b567-ad5eb2451028
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

def Polychromatic418967fa.branch_90 : allB 90 90 :=
  allB_succ' 2 89 90 (Eq.refl Bool.true) (allA_succ_of_accept 1 89 90 (accept_3_4 1 89 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 90)) (allB_succ' 3 88 90 (Eq.refl Bool.true) (allA_succ_of_gcd 2 88 90 2 1 44 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 90
  (Polychromatic418967fa.accept_46_1_42_44_1_3671 1 88 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 90))) (allB_succ' 4 87 90 (Eq.refl Bool.true) (allA_succ_of_gcd 3 87 90 3 1 29 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 87 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 87 90)))) (allB_succ' 5 86 90 (Eq.refl Bool.true) (allA_succ_of_gcd 4 86 90 2 2 43 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 86 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 90 2 1 43 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 90 (accept_3_4 1 86 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86 90)))))
  (allB_succ' 6 85 90 (Eq.refl Bool.true) (allA_succ_of_gcd 5 85 90 5 1 17 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 90 (Polychromatic418967fa.accept_13_4_7_12_1_2823 4
  85 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 90 (accept_3_5 2 85 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 90
  (Polychromatic418967fa.accept_19_1_9_14_1_526 1 85 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 85 90)))))) (allB_succ' 7 84 90 (Eq.refl Bool.true) (allA_succ_of_gcd 6 84 90 6 1 14 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 90
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 5 84 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 90 2 2 42 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 84 90 3 1 28 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 84 90 2 1 42 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 90 (Polychromatic418967fa.accept_17_1_16_5_1_3670 1 84 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 90))))))) (allB_succ' 8 83 90 (Eq.refl Bool.true) (allA_succ_of_accept 7
  83 90 (accept_3_4 7 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 90
  (Polychromatic418967fa.accept_13_6_5_12_1_307 6 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 90 (accept_3_4 4 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 83 90 (Polychromatic418967fa.accept_19_3_7_14_1_3669 3 83 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 90 (Polychromatic418967fa.accept_13_2_5_12_1_2043 2 83 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 90 (accept_3_4 1 83 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 83 90)))))))) (allB_succ' 9 82 90 (Eq.refl Bool.true) (allA_succ_of_gcd 8 82
  90 2 4 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 82
  90 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 82 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 82 90 2 3 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 82 90 (accept_3_5 5 82 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 90 2
  2 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82 90
  (Polychromatic418967fa.accept_12_3_10_6_1_442 3 82 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 82 90 2 1 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 82 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 82 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 82 90))))))))) (allB_succ' 10 81 90 (Eq.refl Bool.true) (allA_succ_of_gcd 9
  81 90 9 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8
  81 90 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 81 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 81 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 90 3 2 27 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 81
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 90
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 81 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 81 90 3 1 27 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 81 90 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 81 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 90 (Polychromatic418967fa.accept_22_1_15_2_1_3668 1 81 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 90)))))))))) (allB_succ' 11 80 90 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 80 90 10 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 90 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 90 2 4 40 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 90 (accept_3_4 7 80 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 80 90 2 3 40 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 80 90 5 1 16 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 80 90 2 2 40 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 90 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 80 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 90 2 1 40 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 90 (accept_3_4 1 80 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 90))))))))))) (allB_succ' 12 79 90 (Eq.refl Bool.true) (allA_succ_of_accept 11 79 90
  (accept_3_5 11 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 79 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 90 (accept_3_5 8 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 79 90 (Polychromatic418967fa.accept_17_7_11_5_1_3539 7 79 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 90 (Polychromatic418967fa.accept_17_6_11_5_1_3506 6 79 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 90 (accept_3_5 5 79 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 79 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 90 (accept_3_5 2 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 90)))))))))))) (allB_succ' 13 78 90 (Eq.refl Bool.true) (allA_succ_of_gcd 12 78 90 6 2 13 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 90
  (Polychromatic418967fa.accept_21_11_15_6_1_3667 11 78 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 90 2 5 39 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 78 90 3 3 26 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 78 90 2 4 39 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 90 (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 78 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 90 6 1 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 90 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 78 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 90 2 2 39 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 78 90 3 1 26 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 78 90 2 1 39 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 90
  (Polychromatic418967fa.accept_19_1_2_14_1_3666 1 78 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 90))))))))))))) (allB_succ' 14 77 90 (Eq.refl Bool.true) (allA_succ_of_accept 13 77 90 (accept_3_4 13 77
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 90
  (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 77 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 90 (accept_3_4 10 77 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 77 90 (Polychromatic418967fa.accept_19_9_1_14_1_1372 9 77 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 90 (Polychromatic418967fa.accept_14_8_7_6_1_1159 8
  77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 90 (accept_3_4 7 77 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 90 (Polychromatic418967fa.accept_19_6_1_14_1_3665 6
  77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 90
  (Polychromatic418967fa.accept_16_5_13_10_1_3664 5 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 90 (accept_3_4 4 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 90 (Polychromatic418967fa.accept_19_2_1_14_1_3663 2 77 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 90 (accept_3_4 1 77 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 90)))))))))))))) (allB_succ' 15 76 90 (Eq.refl Bool.true) (allA_succ_of_gcd 14 76 90 2 7 38
  45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 90
  (Polychromatic418967fa.accept_16_13_12_10_1_3540 13 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 76 90 2 6 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 76 90 (accept_3_5 11 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 90
  2 5 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 90
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 90 2 4 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 90 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 76 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 90 2 3 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 90 (accept_3_5 5 76 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 90 2 2 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 90 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 76 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 90 2 1 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 90 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 76
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 90))))))))))))))) (allB_succ' 16 75 90
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 75 90 15 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 75 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 75 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 90 3 4 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 75 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 90 5 2 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 75 90 3 3 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 90
  (Polychromatic418967fa.accept_11_7_9_2_1_260 7 75 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 75 90 3 2 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 75 90 5 1 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 75 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 90 3 1 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 75 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 90)))))))))))))))) (allB_succ' 17 74 90 (Eq.refl Bool.true) (allA_succ_of_gcd 16 74 90 2 8 37 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 90
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 90 2 7 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 90 (accept_3_4 13 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 90
  2 6 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74
  90 (Polychromatic418967fa.accept_17_11_6_5_1_3662 11 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 90 2 5 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 90 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 74 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 90 2 4 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 90 (accept_3_4 7 74 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 90 2 3 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 74 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 90 2 2 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 74
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 90 2 1 37 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 90 (accept_3_4 1 74
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 90))))))))))))))))) (allB_succ' 18 73 90 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 73 90 (accept_3_5 17 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 73
  90 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 73 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 90 (accept_3_5 14 73 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 73 90 (Polychromatic418967fa.accept_19_13_16_14_1_3517 13 73 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 90
  (Polychromatic418967fa.accept_19_12_16_14_1_3661 12 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 90 (accept_3_5 11 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 73
  90 (Polychromatic418967fa.accept_13_10_8_12_1_2032 10 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 90 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 73 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 90 (accept_3_5 8 73 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 73 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 90 (Polychromatic418967fa.accept_23_6_4_21_1_3660 6
  73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 90 (accept_3_5 5 73 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73 90 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 73
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 73 90 (accept_3_5 2 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 90
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 73 90)))))))))))))))))) (allB_succ' 19 72 90 (Eq.refl Bool.true) (allA_succ_of_gcd 18 72 90 18 1 4 5
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 72 90 2 8 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 72 90 3 5 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 72 90 2 7 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 90 (Polychromatic418967fa.accept_19_13_15_14_1_3549 13 72 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 90 6 2 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 90 2 5 36 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 90 9 1 8 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 90 2 4 36 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 90
  (Polychromatic418967fa.accept_19_7_15_14_1_3659 7 72 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 90 6 1 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 90 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 72 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 90 2 2 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 90 3 1 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 90 2 1 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 90))))))))))))))))))) (allB_succ' 20 71 90
  (Eq.refl Bool.true) (allA_succ_of_accept 19 71 90 (accept_3_4 19 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 71 90 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 71 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 90 (accept_3_4 16 71 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 90 (Polychromatic418967fa.accept_13_2_6_12_1_1334
  15 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 90
  (Polychromatic418967fa.accept_16_14_7_10_1_898 14 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 90 (accept_3_4 13 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71
  90 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 71 90 (Polychromatic418967fa.accept_22_11_5_2_1_3658 11 71 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 90 (accept_3_4 10 71 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 71 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 90 (Polychromatic418967fa.accept_11_8_5_2_1_1629 8
  71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 90 (accept_3_4 7 71 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 90 (Polychromatic418967fa.accept_17_6_3_5_1_3657 6
  71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 90 (accept_3_4 4 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 90
  (Polychromatic418967fa.accept_16_3_7_10_1_3503 3 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 90 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 71 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 90 (accept_3_4 1 71 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 90)))))))))))))))))))) (allB_succ' 21 70 90 (Eq.refl Bool.true) (allA_succ_of_gcd 20 70 90 10
  2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 90
  (Polychromatic418967fa.accept_13_6_5_12_1_307 19 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 90 2 9 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 90 (accept_3_5 17 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 90
  2 8 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 70 90 5
  3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 70 90 2 7
  35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 90
  (Polychromatic418967fa.accept_21_13_7_6_1_3656 13 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 90 2 6 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 90 (accept_3_5 11 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 90
  10 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 90
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 90 2 4 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 90 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 70 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 90 2 3 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 70 90 5 1 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 70 90 2 2 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 90 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 70 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 90 2 1 35 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 90
  (Polychromatic418967fa.accept_13_1_5_12_1_306 1 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 90))))))))))))))))))))) (allB_succ' 22 69 90 (Eq.refl Bool.true) (allA_succ_of_gcd 21 69 90 3 7 23 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 90
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 90 3 6 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 90 (Polychromatic418967fa.accept_19_17_12_14_1_3655 17 69 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 90
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 90 3 5 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 90 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 69 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 90 (Polychromatic418967fa.accept_16_13_5_10_1_1680 13 69 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 90 3 4 23 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 90 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 69 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 90 3 3 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 90 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 69 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 90 3 2 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 90 (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 69 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 90 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 69 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 90 3 1 23 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 90
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 90 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 69 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 90)))))))))))))))))))))) (allB_succ' 23 68 90 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 68 90 2 11 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 68 90 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 68 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 90 2 10 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 90 (accept_3_4 19 68 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 68 90 2 9 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 68 90 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 68 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 90 2 8 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 68
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 90 2 7 34 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 90 (accept_3_4 13 68
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 90 2 6 34 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 90
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 68 90 2 5 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 68 90 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 68 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 90 2 4 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 90 (accept_3_4 7 68 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 68 90 2 3 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 68 90 (Polychromatic418967fa.accept_19_5_11_14_1_3654 5 68 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 90 2 2 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 90 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 68
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 90 2 1 34 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 90 (accept_3_4 1 68
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 90))))))))))))))))))))))) (allB_succ' 24 67 90 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 67 90 (accept_3_5 23 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 67 90 (Polychromatic418967fa.accept_27_22_13_9_1_3653 22 67 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 90 (accept_3_5 20 67 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 19
  67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 90
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 90 (accept_3_5 17 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67
  90 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 67 90 (Polychromatic418967fa.accept_19_15_10_14_1_3652 15 67 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 90 (accept_3_5 14 67 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 67 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 12
  67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 90 (accept_3_5 11 67 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 10
  67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 90 (accept_3_5 8 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 90
  (Polychromatic418967fa.accept_16_7_3_10_1_3614 7 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 90 (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 67 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 90 (accept_3_5 5 67 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 90 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 67 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 67
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 90 (accept_3_5 2 67 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 90)))))))))))))))))))))))) (allB_succ' 25
  66 90 (Eq.refl Bool.true) (allA_succ_of_gcd 24 66 90 6 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 90 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 90 2 11 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 90 3 7 22 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 90 2 10 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 90
  (Polychromatic418967fa.accept_20_19_6_10_1_3651 19 66 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 90 6 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 90 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 66 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 90 2 8 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 90 3 5 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 90 2 7 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 90 (Polychromatic418967fa.accept_17_13_15_5_1_3650 13 66 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 90 6 2 11 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 90
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 90 2 5 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 66 90 3 3 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 66 90 2 4 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 90 (Polychromatic418967fa.accept_17_7_15_5_1_3649 7 66 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 90 6 1 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 90 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 66 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 90 2 2 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 90 3 1 22 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 90 2 1 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 90
  (Polychromatic418967fa.accept_19_1_9_14_1_526 1 66 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 90))))))))))))))))))))))))) (allB_succ' 26 65 90 (Eq.refl Bool.true) (allA_succ_of_gcd 25 65 90 5 5 13 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 65 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 65 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 90 (accept_3_4 22 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 65 90 (Polychromatic418967fa.accept_19_2_8_14_1_3648 21 65 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 90 5 4 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 90 (accept_3_4 19 65 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 65 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 90 (accept_3_4 16 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 65 90
  5 3 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 65
  90 (Polychromatic418967fa.accept_20_14_5_10_1_3647 14 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 65 90 (accept_3_4 13 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 65 90 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 65 90 5 2 13 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 65 90
  (Polychromatic418967fa.accept_16_9_1_10_1_3610 9 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 90 (accept_3_4 7 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 90 (Polychromatic418967fa.accept_19_6_8_14_1_2351 6 65 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 90 5 1 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 90 (accept_3_4 4 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 90 (Polychromatic418967fa.accept_17_2_14_5_1_2575 2
  65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 90 (accept_3_4 1 65 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 90)))))))))))))))))))))))))) (allB_succ' 27 64 90 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 64 90 2 13 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 64 90 (Polychromatic418967fa.accept_17_8_13_5_1_1597 25 64 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 90 2 12 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 90 (accept_3_5 23 64 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 90 2 11 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 64 90 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 64 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 90 2 10 32 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 90
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 90 2 9 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 90 (accept_3_5 17 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 90
  2 8 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 64
  90 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 64 90 2 7 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 64 90 (Polychromatic418967fa.accept_25_13_14_15_1_3646 13 64 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 90 2 6 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 90 (accept_3_5 11 64 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 64 90 2 5 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 64 90 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 64 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 90 2 4 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 90 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 64
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 90 2 3 32 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 90 (accept_3_5 5 64
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 90 2 2 32 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64 90
  (Polychromatic418967fa.accept_12_3_4_6_1_434 3 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 90 2 1 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 90 (Polychromatic418967fa.accept_20_1_4_10_1_3645 1 64 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 90))))))))))))))))))))))))))) (allB_succ' 28 63 90 (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 63 90 9 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 90 3 8 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 90
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 90 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 90 3 7 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 90 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 63 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 90
  (Polychromatic418967fa.accept_20_19_3_10_1_3588 19 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 90 9 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 90 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 63 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 90 3 5 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 90
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 90 3 4 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 90 (Polychromatic418967fa.accept_16_11_15_10_1_3515 11 63 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 90
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 90 9 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 90 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 90 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 63 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 90 3 2 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 90 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 90 3 1 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 63 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 90)))))))))))))))))))))))))))) (allB_succ' 29 62 90 (Eq.refl Bool.true) (allA_succ_of_gcd 28 62 90 2 14
  31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 90
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 90 2 13 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 62 90 (accept_3_4 25 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 90
  2 12 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62
  90 (Polychromatic418967fa.accept_16_7_14_10_1_3544 23 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 62 90 2 11 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 62 90 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 62 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 90 2 10 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 90 (accept_3_4 19 62 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 90 2 9 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 90 (Polychromatic418967fa.accept_19_17_5_14_1_3587 17 62 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 90 2 8 31 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 90
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 90 2 7 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 90 (accept_3_4 13 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 90
  2 6 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62
  90 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 90 2 5 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 90 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 62 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 90 2 4 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 90 (accept_3_4 7 62 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 90 2 3 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 90 (Polychromatic418967fa.accept_16_5_14_10_1_3644 5 62 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 90 2 2 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 90 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 62
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 90 2 1 31 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 90 (accept_3_4 1 62
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 90))))))))))))))))))))))))))))) (allB_succ' 30 61 90 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 61 90 (accept_3_5 29 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 61 90 (Polychromatic418967fa.accept_16_12_13_10_1_2637 28 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 90 (accept_3_5 26 61 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 25
  61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 90
  (Polychromatic418967fa.accept_20_4_1_10_1_3643 24 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 90 (accept_3_5 23 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 61
  90 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 61 90 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 90 (accept_3_5 20 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 61 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 18
  61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 90 (accept_3_5 17 61 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 90 (Polychromatic418967fa.accept_13_3_9_12_1_2062
  16 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 90 (accept_3_5 14 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61
  90 (Polychromatic418967fa.accept_14_13_5_6_1_2747 13 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 61 90 (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 61 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 90 (accept_3_5 11 61 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61 90 (Polychromatic418967fa.accept_13_10_9_12_1_2814 10 61 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 90
  (Polychromatic418967fa.accept_19_9_4_14_1_3642 9 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 90 (accept_3_5 8 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 61 90 (Polychromatic418967fa.accept_22_6_17_2_1_3518 6 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 90 (accept_3_5 5 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 61 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 61 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 90 (accept_3_5 2 61 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 90))))))))))))))))))))))))))))))
  (allB_succ' 31 60 90 (Eq.refl Bool.true) (allA_succ_of_gcd 30 60 90 30 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 90 (Polychromatic418967fa.accept_16_13_12_10_1_3540
  29 60 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 90 2 14 30 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 90 3 9 20 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 90 2 13 30 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 90 5 5 12 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 90 6 4 10 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 90
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 90 2 11 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 60 90 3 7 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 60 90 10 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 90 6 3 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 90 2 8 30 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 90 15 1 4 6 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 90 2 7 30 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 90
  (Polychromatic418967fa.accept_16_13_12_10_1_3540 13 60 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 90 6 2 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 90 (Polychromatic418967fa.accept_16_11_12_10_1_3641 11 60 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 90 10 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 90 3 3 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 90 2 4 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 90 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 60 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 90 6 1 10 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 90 5 1 12 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 60 90 2 2 30 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 90 3 1 20 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 90 2 1 30 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 90
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 60 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 90))))))))))))))))))))))))))))))) (allB_succ' 32 59 90 (Eq.refl Bool.true) (allA_succ_of_accept 31 59 90
  (accept_3_4 31 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 59 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 90 (accept_3_4 28 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 59 90 (Polychromatic418967fa.accept_19_8_2_14_1_3640 27 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 90 (Polychromatic418967fa.accept_19_7_2_14_1_3569
  26 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 90 (accept_3_4 25 59
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 90
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 59 90 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 90 (accept_3_4 22 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 59 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 90 (Polychromatic418967fa.accept_11_9_4_2_1_600 20
  59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 90 (accept_3_4 19 59 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 90 (Polychromatic418967fa.accept_7_4_3_6_1_340 18
  59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 90 (accept_3_4 16 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59
  90 (Polychromatic418967fa.accept_16_15_11_10_1_3639 15 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 90 (Polychromatic418967fa.accept_27_14_5_9_1_3638 14 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 90 (accept_3_4 13 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 90 (Polychromatic418967fa.accept_16_12_11_10_1_1667 12 59 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 90
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 90 (accept_3_4 10 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59
  90 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 90 (Polychromatic418967fa.accept_13_8_7_12_1_3637 8 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 90 (accept_3_4 7 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 90 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 90 (accept_3_4 4 59 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 90 (Polychromatic418967fa.accept_17_3_8_5_1_3636 3
  59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 90 (accept_3_4 1 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  90)))))))))))))))))))))))))))))))) (allB_succ' 33 58 90 (Eq.refl Bool.true) (allA_succ_of_gcd 32 58 90 2 16 29 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 90 2 15 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 90 (accept_3_5 29 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 90
  2 14 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58
  90 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 58 90 2 13 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 58 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 58 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 90 2 12 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 90 (accept_3_5 23 58 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 58 90 2 11 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 90 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 58 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 90 2 10 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 90 (Polychromatic418967fa.accept_22_19_14_2_1_3635
  19 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 90 2 9 29 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 90 (accept_3_5 17 58
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58 90 2 8 29 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 58 90
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 58 90 2 7 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 58 90 (Polychromatic418967fa.accept_19_13_1_14_1_3634 13 58 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 90 2 6 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 90 (accept_3_5 11 58 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 58 90 2 5 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 58 90 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 58 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 58 90 2 4 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 58 90 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7
  58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 90 2 3 29 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 90 (accept_3_5 5 58
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 90 2 2 29 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 58 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 58 90 2 1 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 58 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 58 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 58 90))))))))))))))))))))))))))))))))) (allB_succ' 34 57 90 (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 57 90 3 11 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 57 90 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  57 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 90 3 10 19 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 90
  (Polychromatic418967fa.accept_20_9_17_10_1_3633 29 57 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 90 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 57 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 90 3 9 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 90 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 57 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 90
  (Polychromatic418967fa.accept_20_5_17_10_1_3632 25 57 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 90 3 8 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 90 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 57 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 90 3 7 19 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 90
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 57 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 90 3 6 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 90 (Polychromatic418967fa.accept_13_4_5_12_1_751 17 57 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 90
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 57 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 90 3 5 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 90 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 57 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 90 (Polychromatic418967fa.accept_20_13_17_10_1_3631 13 57
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 90 3 4 19 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 90 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 57 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 90 3 3 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 90 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 57 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 90 3 2 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 90 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 57 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 90 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 57 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 90 3 1 19 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 90
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 57 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 90 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 57 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 90)))))))))))))))))))))))))))))))))) (allB_succ' 35 56 90 (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 56 90 2 17 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 56 90 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 56 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 90 2 16 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 90 (accept_3_4 31 56 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 90 2 15 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 56 90 (Polychromatic418967fa.accept_13_3_4_12_1_36 29 56 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 90 2 14 28 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 90
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 90 2 13 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 56 90 (accept_3_4 25 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 90
  2 12 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56
  90 (Polychromatic418967fa.accept_19_4_18_14_1_3630 23 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 56 90 2 11 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 56 90 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 56 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 90 2 10 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 90 (accept_3_4 19 56 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 90 2 9 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 56 90 (Polychromatic418967fa.accept_25_17_6_15_1_3629 17 56 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 90 2 8 28 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 90
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 90 2 7 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 90 (accept_3_4 13 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 90
  2 6 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56
  90 (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 90 2 5 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 90 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 56 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 90 2 4 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 90 (accept_3_4 7 56 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 56 90 2 3 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 56 90 (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 56 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 90 2 2 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 90 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3
  56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 90 2 1 28 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 90 (accept_3_4 1 56
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 90))))))))))))))))))))))))))))))))))) (allB_succ' 36 55 90
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 55 90 5 7 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 55 90 (Polychromatic418967fa.accept_19_15_17_14_1_1370 34 55 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 90 (accept_3_5 32 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55
  90 (Polychromatic418967fa.accept_19_12_17_14_1_3519 31 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 55 90 5 6 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 55 90 (accept_3_5 29 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 55 90 (Polychromatic418967fa.accept_13_2_3_12_1_735 28 55 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 90 (Polychromatic418967fa.accept_20_7_15_10_1_3628 27 55 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 90 (accept_3_5 26 55 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55 90 5 5 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 55 90 (Polychromatic418967fa.accept_19_5_17_14_1_3627
  24 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 90 (accept_3_5 23 55
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 90
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 22 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 55 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 90 5 4 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 90 (Polychromatic418967fa.accept_14_5_13_6_1_3574 19 55 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 90
  (Polychromatic418967fa.accept_17_1_4_5_1_3501 18 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 90 (accept_3_5 17 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55
  90 (Polychromatic418967fa.accept_17_16_4_5_1_3626 16 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 55 90 5 3 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 55 90 (accept_3_5 14 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 55 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 90 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 55 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 90 (accept_3_5 11 55 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55 90 5 2 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 55 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 90 (accept_3_5 8 55 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 90 (Polychromatic418967fa.accept_14_7_13_6_1_1177 7 55 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 90
  (Polychromatic418967fa.accept_17_6_4_5_1_3625 6 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 55 90 5 1 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 55 90 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 55 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 90 (Polychromatic418967fa.accept_16_3_7_10_1_3503 3 55 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 90 (accept_3_5 2 55 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 90))))))))))))))))))))))))))))))))))))
  (allB_succ' 37 54 90 (Eq.refl Bool.true) (allA_succ_of_gcd 36 54 90 18 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 90 (Polychromatic418967fa.accept_20_15_14_10_1_2317
  35 54 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 90 2 17 27 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 54 90 3 11 18 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 54 90 2 16 27 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 90
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 54 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 90 6 5 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 54 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 90 2 14 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 90 9 3 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 90 2 13 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 54 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 90 6 4 9 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 90
  (Polychromatic418967fa.accept_11_1_10_2_1_58 23 54 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 90 2 11 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 54 90 3 7 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 54 90 2 10 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 54 90 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 54 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 90 18 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 90 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 54 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 90 2 8 27 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 90 3 5 18 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 90 2 7 27 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 90
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 54 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 90 6 2 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 90 2 5 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 90 9 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 90 2 4 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 90 (Polychromatic418967fa.accept_21_7_12_6_1_3624 7 54 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 90 6 1 9 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 90
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 54 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 54 90 2 2 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 54 90 3 1 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 54 90 2 1 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 54 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 90))))))))))))))))))))))))))))))))))))) (allB_succ' 38 53 90 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 53 90 (accept_3_4 37 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 53 90 (Polychromatic418967fa.accept_19_17_15_14_1_3623 36 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 90 (accept_3_4 34 53 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 33
  53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 90
  (Polychromatic418967fa.accept_19_13_15_14_1_3549 32 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 90 (accept_3_4 31 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53
  90 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 53 90 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 90 (accept_3_4 28 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 53 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 26
  53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 90 (accept_3_4 25 53 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 24
  53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 90 (accept_3_4 22 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53
  90 (Polychromatic418967fa.accept_13_8_1_12_1_762 21 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 53 90 (Polychromatic418967fa.accept_17_3_2_5_1_2556 20 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 90 (accept_3_4 19 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 53 90 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 53 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 90 (accept_3_4 16 53 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 90
  (Polychromatic418967fa.accept_16_14_5_10_1_3622 14 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 90 (accept_3_4 13 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53
  90 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 53 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 90 (accept_3_4 10 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 53 90 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 53 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 90 (Polychromatic418967fa.accept_13_8_1_12_1_762 8
  53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 90 (accept_3_4 7 53 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 90 (Polychromatic418967fa.accept_24_6_5_18_1_3621 6
  53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 90
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 90 (accept_3_4 4 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 90 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 90 (accept_3_4 1 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 90)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 52 90 (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 52 90 2 19 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 52 90 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 52 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 90 2 18 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 90 (accept_3_5 35 52 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 52 90 2 17 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 52 90 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 52 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 90 2 16 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 90 (Polychromatic418967fa.accept_14_3_10_6_1_1136
  31 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 90 2 15 26 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 90 (accept_3_5 29 52
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 90 2 14 26 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 90
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 90 2 13 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 90 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 52 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 90 2 12 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 90 (accept_3_5 23 52 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 52 90 2 11 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 52 90 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 52 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 90 2 10 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 90 (Polychromatic418967fa.accept_32_19_20_26_1_3620
  19 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 90 2 9 26 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 90 (accept_3_5 17 52
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 90 2 8 26 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 90
  (Polychromatic418967fa.accept_12_3_4_6_1_434 15 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 52 90 2 7 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 52 90 (Polychromatic418967fa.accept_20_13_12_10_1_3619 13 52 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 90 2 6 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 90 (accept_3_5 11 52 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 52 90 2 5 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 52 90 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 52 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 90 2 4 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 90 (Polychromatic418967fa.accept_27_7_25_9_1_3618 7 52 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 90 2 3 26 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 90 (accept_3_5 5 52 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 90 2 2 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52 90 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 52 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 90 2 1 26 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 90
  (Polychromatic418967fa.accept_25_1_2_15_1_3617 1 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 90))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 51 90 (Eq.refl Bool.true) (allA_succ_of_gcd 39
  51 90 3 13 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  38 51 90 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 51 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 90 3 12 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 90 (Polychromatic418967fa.accept_19_16_13_14_1_3616
  35 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 90
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 51 90 3 11 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 51 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 51 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 90 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 51 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 90 3 10 17 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 90 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 51 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 90 3 9 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 51 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 51 90 3 8 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 51 90 (Polychromatic418967fa.accept_16_7_3_10_1_3614 23 51 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 51 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 90 3 7 17 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 90
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 90 (Polychromatic418967fa.accept_20_19_11_10_1_3615 19 51 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 90 3 6 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 90
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 90 3 5 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 51 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 90 3 4 17 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 90
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 90 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 51 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 90 3 3 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 90
  (Polychromatic418967fa.accept_16_7_3_10_1_3614 7 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 90 3 2 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 51 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 90 3 1 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 90
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 51 90)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 50 90 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 50 90 10 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 90 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 50 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 90 2 19 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 90 (accept_3_4 37 50 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 50 90 2 18 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 50 90 5 7 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 50 90 2 17 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 50 90 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 50 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 90 2 16 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 90 (accept_3_4 31 50 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 90 10 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 50 90 (Polychromatic418967fa.accept_19_10_12_14_1_3613 29 50 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 90 2 14 25 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 90
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 50 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 90 2 13 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 50 90 5 5 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 50 90 2 12 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 50 90 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 50 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 90 2 11 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 90 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 50 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 90 10 2 5 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 90 (accept_3_4 19 50 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 90 2 9 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 50 90 (Polychromatic418967fa.accept_13_4_11_12_1_1318
  17 50 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 90 2 8 25 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 50 90 5 3 10 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 50 90 2 7 25 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 90 (accept_3_4 13 50
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 90 2 6 25 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 90
  (Polychromatic418967fa.accept_17_11_16_5_1_3612 11 50 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 90 10 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 90 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 50 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 90 2 4 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 90 (accept_3_4 7 50 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 90 2 3 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 50 90 5 1 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 50 90 2 2 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 50 90 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 50 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 90 2 1 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 90 (accept_3_4 1 50 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 90))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 49 90 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 49 90 (accept_3_5 41 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49
  90 (Polychromatic418967fa.accept_22_18_5_2_1_3611 40 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 90 (accept_3_5 38 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 90 (Polychromatic418967fa.accept_13_11_10_12_1_1338 37 49 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 90
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 90 (accept_3_5 35 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49
  90 (Polychromatic418967fa.accept_13_8_10_12_1_1337 34 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 90 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 90 (accept_3_5 32 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 90
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 90 (accept_3_5 29 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49
  90 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 90 (accept_3_5 26 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 90 (Polychromatic418967fa.accept_16_9_1_10_1_3610 25 49 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 90
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 90 (accept_3_5 23 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49
  90 (Polychromatic418967fa.accept_13_9_10_12_1_2048 22 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 90 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 90 (accept_3_5 20 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 90
  (Polychromatic418967fa.accept_21_18_7_6_1_3609 18 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 90 (accept_3_5 17 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49
  90 (Polychromatic418967fa.accept_19_16_11_14_1_3608 16 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 90 (accept_3_5 14 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 90 (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 49 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 90
  (Polychromatic418967fa.accept_21_12_7_6_1_3607 12 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 90 (accept_3_5 11 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49
  90 (Polychromatic418967fa.accept_17_10_15_5_1_3606 10 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 90 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 90 (accept_3_5 8 49 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 49 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 90 (Polychromatic418967fa.accept_13_6_10_12_1_2049
  6 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 90 (accept_3_5 5 49 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 90 (Polychromatic418967fa.accept_21_4_7_6_1_3605 4
  49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 90 (accept_3_5 2 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 90
  (Polychromatic418967fa.accept_14_1_7_6_1_3604 1 49 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 90)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 48 90 (Eq.refl Bool.true) (allA_succ_of_gcd
  42 48 90 6 7 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 48 90 (Polychromatic418967fa.accept_27_14_21_9_1_3603 41 48 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 90 2 20 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 48 90 3 13 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 48 90 2 19 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 48 90 (Polychromatic418967fa.accept_19_18_10_14_1_2392 37 48 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 90 6 6 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 90 (Polychromatic418967fa.accept_20_15_8_10_1_3602
  35 48 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 90 2 17 24 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 48 90 3 11 16 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 48 90 2 16 24 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 90
  (Polychromatic418967fa.accept_11_9_4_2_1_600 31 48 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 90 6 5 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 90 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 48 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 90 2 14 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 48 90 3 9 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 48 90 2 13 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 90 (Polychromatic418967fa.accept_19_6_10_14_1_3542 25 48 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 90 6 4 8 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 90
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 48 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 90 2 11 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 48 90 3 7 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 48 90 2 10 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 90 (Polychromatic418967fa.accept_17_2_14_5_1_2575 19 48 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 90 6 3 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 90 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 48 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 90 2 8 24 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 90 3 5 16 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 90 2 7 24 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 90
  (Polychromatic418967fa.accept_22_13_4_2_1_3601 13 48 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 90 6 2 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 90 (Polychromatic418967fa.accept_23_11_2_21_1_3600 11 48 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 90 2 5 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 90 3 3 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 90 2 4 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 90 (Polychromatic418967fa.accept_19_7_10_14_1_3599 7 48 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 90 6 1 8 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 90
  (Polychromatic418967fa.accept_19_5_10_14_1_3598 5 48 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 90 2 2 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 48 90 3 1 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 48 90 2 1 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 90 (Polychromatic418967fa.accept_19_1_10_14_1_3597 1 48 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 90))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 47 90
  (Eq.refl Bool.true) (allA_succ_of_accept 43 47 90 (accept_3_4 43 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 47 90 (Polychromatic418967fa.accept_17_8_13_5_1_1597 42 47 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 90 (accept_3_4 40 47 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 39
  47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 90
  (Polychromatic418967fa.accept_20_18_7_10_1_3596 38 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 90 (accept_3_4 37 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47
  90 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 47 90 (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 47 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 90 (accept_3_4 34 47 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 47 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 90 (accept_3_4 31 47 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 90 (Polychromatic418967fa.accept_13_4_8_12_1_3526
  30 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 90 (accept_3_4 28 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47
  90 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 90 (Polychromatic418967fa.accept_17_9_13_5_1_3512 26 47 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 90 (accept_3_4 25 47 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 90 (Polychromatic418967fa.accept_19_5_9_14_1_3505 24 47 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 90
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 90 (accept_3_4 22 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47
  90 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 90 (Polychromatic418967fa.accept_13_7_8_12_1_2810 20 47 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 90 (accept_3_4 19 47 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 90 (accept_3_4 16 47 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 90
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 90 (accept_3_4 13 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47
  90 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 47 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 90 (accept_3_4 10 47 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 47 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 90 (accept_3_4 7 47 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 90 (Polychromatic418967fa.accept_19_6_9_14_1_3541 6
  47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 90 (accept_3_4 4 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 90
  (Polychromatic418967fa.accept_19_3_9_14_1_3595 3 47 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 90 (Polychromatic418967fa.accept_24_2_23_18_1_3594 2 47 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 90 (accept_3_4 1 47 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 90)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 46 90 (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 46 90 2 22 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 90 (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 46 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 90 2 21 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 90 (accept_3_5 41 46 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 46 90 2 20 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 46 90 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 46 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 90 2 19 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 90 (Polychromatic418967fa.accept_7_2_4_6_1_166 37
  46 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 90 2 18 23 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 90 (accept_3_5 35 46
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 90 2 17 23 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 90
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 46 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 46 90 2 16 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 46 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 46 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 90 2 15 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 90 (accept_3_5 29 46 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 46 90 2 14 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 90 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 46 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 90 2 13 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 90 (Polychromatic418967fa.accept_17_8_12_5_1_1577
  25 46 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 90 2 12 23 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 90 (accept_3_5 23 46
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 90 2 11 23 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 90
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 46 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 90 2 10 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 46 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 90 2 9 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 90 (accept_3_5 17 46 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 90 2 8 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 90 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 46 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 90 2 7 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 90 (Polychromatic418967fa.accept_16_13_14_10_1_1669
  13 46 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 90 2 6 23 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 90 (accept_3_5 11 46
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 90 2 5 23 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 90
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 46 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 90 2 4 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 90 (Polychromatic418967fa.accept_16_7_14_10_1_3544 7 46 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 90 2 3 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 90 (accept_3_5 5 46 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 90 2 2 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 46 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 90 2 1 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 90 (Polychromatic418967fa.accept_27_1_19_9_1_3593 1
  46 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  90))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 90 (allA_succ_of_accept 44 45 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 90 3 14 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 90 (Polychromatic418967fa.accept_13_2_6_12_1_1334 41 45 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 90 5 8 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 45 90 3 13 15 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 90
  (Polychromatic418967fa.accept_12_2_9_6_1_439 38 45 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 90 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 45 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 90 9 4 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 45 90 5 7 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 90 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 45 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 90 3 11 15 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 90
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 45 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 90 15 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 90 (Polychromatic418967fa.accept_19_10_7_14_1_3592 29 45 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 90
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 45 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 90 9 3 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 90 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 45 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 90 5 5 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 45 90 3 8 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 90
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 45 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 90 3 7 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 45 90 5 4 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 90 9 2 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 90 (Polychromatic418967fa.accept_20_17_5_10_1_3591 17 45 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 45 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 90 15 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 90 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 45 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 90 (Polychromatic418967fa.accept_20_13_5_10_1_3590 13 45 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 90 3 4 15 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 45 90 5 2 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 45 90 9 1 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 90 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 45 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 90 3 2 15 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 45 90 5 1 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 90
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 45 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 90 3 1 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 90 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 45 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 90 (Polychromatic418967fa.accept_20_1_5_10_1_3534 1 45 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 90)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 44 90 (allA_succ_of_accept 43 44 90 (accept_3_4 43 44 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 44 90 2 21 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 90 (Polychromatic418967fa.accept_13_2_5_12_1_2043 41 44 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 90 2 20 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 44 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 90 2 19 22 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 90 (accept_3_4 37 44 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 90 2 18 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 90 (Polychromatic418967fa.accept_16_3_12_10_1_315
  35 44 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 90 2 17 22 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 90
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 44 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 90 2 16 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 90 (accept_3_4 31 44 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 90
  2 15 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44
  90 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 44 90 2 14 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 44 90 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 44 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 90 2 13 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 90 (accept_3_4 25 44 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 44 90 2 12 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 44 90 (Polychromatic418967fa.accept_25_23_19_15_1_3589 23 44 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 90 2 11 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 90 (Polychromatic418967fa.accept_12_9_8_6_1_466 21
  44 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 90 2 10 22 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 90 (accept_3_4 19 44
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 90 2 9 22 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 44 90 2 8 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 44 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 44 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 90 2 7 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 90 (accept_3_4 13 44 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 44 90 2 6 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 44 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 44 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 90 2 5 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 90 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 44
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 90 2 4 22 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 90 (accept_3_4 7 44
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 90 2 3 22 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44 90
  (Polychromatic418967fa.accept_16_5_12_10_1_3508 5 44 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 90 2 2 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 90 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 90 2 1 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 90 (accept_3_4 1 44 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 90)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 90 (allA_succ_of_accept 42 43 90
  (Polychromatic418967fa.accept_13_3_4_12_1_36 42 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 90 (accept_3_5 41 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43
  90 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 43 90 (Polychromatic418967fa.accept_20_19_3_10_1_3588 39 43 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 90 (accept_3_5 38 43 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 43 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 90 (Polychromatic418967fa.accept_19_17_5_14_1_3587
  36 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 90 (accept_3_5 35 43
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 90 (Polychromatic418967fa.accept_11_1_10_2_1_58
  34 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 90 (accept_3_5 32 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43
  90 (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 90 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 43 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 90 (accept_3_5 29 43 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 90 (Polychromatic418967fa.accept_13_2_4_12_1_745 28 43 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 90
  (Polychromatic418967fa.accept_19_8_5_14_1_3586 27 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 90 (accept_3_5 26 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43
  90 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 43 90 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 43 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 90 (accept_3_5 23 43 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 43 90 (Polychromatic418967fa.accept_19_3_5_14_1_3584 22 43 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 90 (accept_3_5 20 43 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 90 (Polychromatic418967fa.accept_7_5_1_6_1_163 19
  43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 90
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 90 (accept_3_5 17 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43
  90 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 43 90 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 43 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 90 (accept_3_5 14 43 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 43 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 90 (Polychromatic418967fa.accept_7_5_1_6_1_163 12
  43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 90 (accept_3_5 11 43 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 90 (Polychromatic418967fa.accept_19_10_5_14_1_3583
  10 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 90 (accept_3_5 8 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 90
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 90 (Polychromatic418967fa.accept_19_6_5_14_1_3582 6 43 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 90 (accept_3_5 5 43 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 90 (Polychromatic418967fa.accept_22_4_21_2_1_3581 4 43 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 90 (Polychromatic418967fa.accept_13_3_4_12_1_36 3
  43 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 90 (accept_3_5 2 43 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  90))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 90 (allA_succ_of_accept 41 42 90
  (Polychromatic418967fa.accept_13_2_3_12_1_735 41 42 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 90 2 20 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 42 90 3 13 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 42 90 2 19 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 90 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 42 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 90 6 6 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 90 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 42 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 90 2 17 21 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 42 90 3 11 14 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 42 90 2 16 21 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 90
  (Polychromatic418967fa.accept_23_8_19_21_1_3580 31 42 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 90 6 5 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 90 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 42 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 90 2 14 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 90 3 9 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 90 2 13 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 90 (Polychromatic418967fa.accept_20_5_2_10_1_3576 25 42 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 90 6 4 7 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 90
  (Polychromatic418967fa.accept_20_3_2_10_1_3579 23 42 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 90 2 11 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 42 90 3 7 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 42 90 2 10 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 90 (Polychromatic418967fa.accept_22_19_20_2_1_3578 19 42 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 90 6 3 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 90 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 42 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 90 2 8 21 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 42 90 3 5 14 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 90 2 7 21 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 90
  (Polychromatic418967fa.accept_17_13_8_5_1_3532 13 42 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 90 6 2 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 90 (Polychromatic418967fa.accept_22_11_20_2_1_3577 11 42 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 90 2 5 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 90 3 3 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 90 2 4 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 90 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 42 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 90 6 1 7 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 90
  (Polychromatic418967fa.accept_20_5_2_10_1_3576 5 42 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 90 2 2 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 42 90 3 1 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 42 90 2 1 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 90 (Polychromatic418967fa.accept_25_1_17_15_1_3575 1 42 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 90)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 90
  (allA_succ_of_accept 40 41 90 (accept_3_4 40 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41
  90 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 90 (Polychromatic418967fa.accept_11_5_8_2_1_588 38 41 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 90 (accept_3_4 37 41 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 90 (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 41 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 90 (accept_3_4 34 41 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 90 (Polychromatic418967fa.accept_14_5_13_6_1_3574
  33 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 90
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 32 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 90 (accept_3_4 31 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  90 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 90 (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 41 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 90 (accept_3_4 28 41 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 90
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 90 (accept_3_4 25 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41
  90 (Polychromatic418967fa.accept_19_5_3_14_1_3573 24 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 90 (accept_3_4 22 41 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 90 (Polychromatic418967fa.accept_14_7_13_6_1_1177 21 41 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 90
  (Polychromatic418967fa.accept_22_20_19_2_1_3572 20 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 90 (accept_3_4 19 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41
  90 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 90 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 41 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 90 (accept_3_4 16 41 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 90
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 14 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 90 (accept_3_4 13 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  90 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 90 (accept_3_4 10 41 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 90 (Polychromatic418967fa.accept_17_9_7_5_1_1566 9 41 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 90
  (Polychromatic418967fa.accept_19_8_3_14_1_3571 8 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 90 (accept_3_4 7 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 90
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 90 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 41 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 90 (accept_3_4 4 41 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 90 (Polychromatic418967fa.accept_21_2_20_6_1_2277 2
  41 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 90 (accept_3_4 1 41 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 90))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 90
  (allA_succ_of_accept 39 40 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 40 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 90 2 19 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 90 (Polychromatic418967fa.accept_13_11_1_12_1_742 37 40 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 90 2 18 20 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 40 90 5 7 8 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 40 90 2 17 20 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 90
  (Polychromatic418967fa.accept_12_9_4_6_1_460 33 40 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 40 90 2 16 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 40 90 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 40 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 90 10 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 90 (accept_3_5 29 40 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 40 90 2 14 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 40 90 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 40 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 90 2 13 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 40 90 5 5 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 40 90 2 12 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 90 (accept_3_5 23 40 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 90 2 11 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 40 90 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 40 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 90 10 2 4 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 90
  (Polychromatic418967fa.accept_23_19_17_21_1_3570 19 40 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 40 90 2 9 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 40 90 (accept_3_5 17 40 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 90
  2 8 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 40 90 5
  3 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 40 90 2 7
  20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 90
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 40 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 90 2 6 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 90 (accept_3_5 11 40 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 90
  10 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 90
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 40 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 90 2 4 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 90 (Polychromatic418967fa.accept_19_7_2_14_1_3569 7 40 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 90 2 3 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 40 90 5 1 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 40 90 2 2 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 90 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 40 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 90 2 1 20 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 90
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 40 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 90)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 90 (allA_succ_of_accept 38 39 90
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 90 3 12 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 90 (Polychromatic418967fa.accept_16_3_7_10_1_3503 35 39 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 90
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 90 3 11 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 90 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 39 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 39 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 90 3 10 13 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 90 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 39 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 90 3 9 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 39 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 90 3 8 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 90 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 39 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 90 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 39 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 90 3 7 13 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 90
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 39 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 90 3 6 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 90
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 90 3 5 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 39 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 90 3 4 13 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 90
  (Polychromatic418967fa.accept_20_11_19_10_1_3568 11 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 39 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 90 3 3 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 90 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 39 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 90
  (Polychromatic418967fa.accept_20_7_19_10_1_3567 7 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 90 3 2 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 90 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 39 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 90 3 1 13 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 90
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 39 90))))))))))))))))))))))))))))))))))))))) (allB_succ 38 90 (allA_succ_of_accept 37
  38 90 (accept_3_4 37 38 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38 90 2 18 19 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 38 90
  (Polychromatic418967fa.accept_17_1_4_5_1_3501 35 38 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 38 90 2 17 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 38 90 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 38 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 90 2 16 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 90 (accept_3_4 31 38 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 38 90 2 15 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 38 90 (Polychromatic418967fa.accept_23_6_15_21_1_3566 29 38 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 38 90 2 14 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 38 90 (Polychromatic418967fa.accept_12_3_2_6_1_138 27
  38 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 90 2 13 19 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 90 (accept_3_4 25 38
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 90 2 12 19 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 38 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 38 90 2 11 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 38 90 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 38 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 90 2 10 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 90 (accept_3_4 19 38 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 38 90 2 9 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 38 90 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 38 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 90 2 8 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 90 (Polychromatic418967fa.accept_12_3_2_6_1_138 15
  38 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 90 2 7 19 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 90 (accept_3_4 13 38
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 90 2 6 19 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 90
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 38 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 90 2 5 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 90 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 38 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 90 2 4 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 38 90 (accept_3_4 7 38 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 38 90 2 3 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 38 90 (Polychromatic418967fa.accept_20_5_18_10_1_3565 5 38 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 90 2 2 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 90 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 38 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 90 2 1 19 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 90 (accept_3_4 1 38 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 38 90)))))))))))))))))))))))))))))))))))))) (allB_succ 37 90
  (allA_succ_of_accept 36 37 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 90 (accept_3_5 35 37 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 90 (Polychromatic418967fa.accept_19_15_18_14_1_3564 34 37 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 90
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 90 (accept_3_5 32 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37
  90 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 90 (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 37 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 90 (accept_3_5 29 37 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 90 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 37 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 90 (accept_3_5 26 37 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 25
  37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 90 (accept_3_5 23 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37
  90 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 37 90 (Polychromatic418967fa.accept_20_1_17_10_1_3563 21 37 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 90 (accept_3_5 20 37 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 37 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 18
  37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 90 (accept_3_5 17 37 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 90
  (Polychromatic418967fa.accept_19_16_18_14_1_3562 16 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 37 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 90 (accept_3_5 14 37 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 37 90 (Polychromatic418967fa.accept_16_13_5_10_1_1680 13 37 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 90 (Polychromatic418967fa.accept_16_12_5_10_1_3561
  12 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 90 (accept_3_5 11 37
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 90 (Polychromatic418967fa.accept_7_3_2_6_1_56
  10 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 90
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 90 (accept_3_5 8 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 90 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 37 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 90 (accept_3_5 5 37 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 37 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 90 (accept_3_5 2 37 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 90)))))))))))))))))))))))))))))))))))))
  (allB_succ 36 90 (allA_succ_of_accept 35 36 90 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 36 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 90 2 17 18 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 90 3 11 12 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 90 2 16 18 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 90
  (Polychromatic418967fa.accept_17_14_2_5_1_3560 31 36 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 90 6 5 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 90 (Polychromatic418967fa.accept_20_9_16_10_1_3559 29 36 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 90 2 14 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 36 90 9 3 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 36 90 2 13 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 90 (Polychromatic418967fa.accept_20_5_16_10_1_3558 25 36 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 90 6 4 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 90
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 36 90 2 11 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 36 90 3 7 12 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 36 90 2 10 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 36 90 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 90 18 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 90 (Polychromatic418967fa.accept_21_17_15_6_1_3557 17 36 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 90 2 8 18 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 90 3 5 12 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 90 2 7 18 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 90
  (Polychromatic418967fa.accept_21_13_15_6_1_3556 13 36 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 90 6 2 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 90 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 36 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 90 2 5 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 36 90 9 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 36 90 2 4 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 90 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 36 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 90 6 1 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 90
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 90 2 2 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 36 90 3 1 12 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 36 90 2 1 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 90 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 36 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 90)))))))))))))))))))))))))))))))))))) (allB_succ 35 90
  (allA_succ_of_accept 34 35 90 (accept_3_4 34 35 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35
  90 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 90 (Polychromatic418967fa.accept_19_13_16_14_1_3517 32 35 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 90 (accept_3_4 31 35 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 90 5 6 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 90 (accept_3_4 28 35 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 90 (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 35 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 90
  (Polychromatic418967fa.accept_20_6_15_10_1_3555 26 35 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 90 5 5 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 90 (Polychromatic418967fa.accept_19_5_16_14_1_2374 24 35 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 90 (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 35 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 90 (accept_3_4 22 35 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 90 5 4 7 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 90 (accept_3_4 19 35
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 90
  (Polychromatic418967fa.accept_19_18_16_14_1_2377 18 35 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 90 (accept_3_4 16 35 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 90 5 3 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 35 90 (Polychromatic418967fa.accept_20_14_15_10_1_3554 14 35 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 90 (accept_3_4 13 35 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 90 (Polychromatic418967fa.accept_16_12_3_10_1_3524 12 35 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 90
  (Polychromatic418967fa.accept_19_11_16_14_1_3553 11 35 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 90 5 2 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 90 (Polychromatic418967fa.accept_13_8_9_12_1_2813 8 35 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 90 (accept_3_4 7 35 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 90 (Polychromatic418967fa.accept_17_6_1_5_1_3552 6 35 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 90 5 1 7 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 90 (accept_3_4 4 35 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 90 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 35 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 90
  (Polychromatic418967fa.accept_19_2_16_14_1_3551 2 35 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 90 (accept_3_4 1 35 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  90))))))))))))))))))))))))))))))))))) (allB_succ 34 90 (allA_succ_of_accept 33 34 90
  (Polychromatic418967fa.accept_12_9_10_6_1_872 33 34 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 90 2 16 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 90 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 34 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 90 2 15 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 90 (accept_3_5 29 34 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 34 90 2 14 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 90 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 34 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 90 2 13 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 90 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25
  34 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 90 2 12 17 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 90 (accept_3_5 23 34
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 90 2 11 17 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 90
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 34 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 90 2 10 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 90 (Polychromatic418967fa.accept_21_19_13_6_1_3550 19 34 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 90 2 9 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 90 (accept_3_5 17 34 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 90 2 8 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 90 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 34 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 90 2 7 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 90 (Polychromatic418967fa.accept_19_13_15_14_1_3549
  13 34 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 90 2 6 17 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 90 (accept_3_5 11 34
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 90 2 5 17 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 90
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 34 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 90 2 4 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 90 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 34 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 90 2 3 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 90 (accept_3_5 5 34 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 90 2 2 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 90 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 34 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 90 2 1 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 90 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1
  34 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 90))))))))))))))))))))))))))))))))))
  (allB_succ 33 90 (allA_succ_of_accept 32 33 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 90 3 10 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 33 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 90 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 33 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 90 3 9 11 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 90
  (Polychromatic418967fa.accept_12_2_9_6_1_439 26 33 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 33 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 90 3 8 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 90
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 33 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 90 3 7 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 90 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 33 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 90 3 6 11 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 90
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 33 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 90 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 33 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 90 3 5 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 90 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 33 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 90
  (Polychromatic418967fa.accept_14_13_5_6_1_2747 13 33 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 90 3 4 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 90 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 33 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 90 3 3 11 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 90
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 90 3 2 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 90 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 33 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 90
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 33 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 90 3 1 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 90 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 33 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 33 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 90)))))))))))))))))))))))))))))))))
  (allB_succ 32 90 (allA_succ_of_accept 31 32 90 (accept_3_4 31 32 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 32 90 2 15 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 32 90 (Polychromatic418967fa.accept_27_2_5_9_1_3548 29 32 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 32 90 2 14 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 32 90 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 32 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 90 2 13 16 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 90 (accept_3_4 25 32 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 90 2 12 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 90 (Polychromatic418967fa.accept_7_2_4_6_1_166 23
  32 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 90 2 11 16 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 90
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 32 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 90 2 10 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 90 (accept_3_4 19 32 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 90
  2 9 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32
  90 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 32 90 2 8 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 32 90 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 32 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 90 2 7 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 90 (accept_3_4 13 32 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 32 90 2 6 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 32 90 (Polychromatic418967fa.accept_17_11_15_5_1_3547 11 32 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 90 2 5 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 90 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 90 2 4 16 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 90 (accept_3_4 7 32
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 90 2 3 16 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 90
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 90 2 2 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 90 2 1 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 90 (accept_3_4 1 32 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 90)))))))))))))))))))))))))))))))) (allB_succ 31 90 (allA_succ_of_accept 30 31 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 90 (accept_3_5 29 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31
  90 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 90 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 31 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 90 (accept_3_5 26 31 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 90
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 90 (accept_3_5 23 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31
  90 (Polychromatic418967fa.accept_25_22_6_15_1_3546 22 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 90 (accept_3_5 20 31 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 90 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 31 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 90
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 90 (accept_3_5 17 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 31
  90 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 31 90 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 31 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 90 (accept_3_5 14 31 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 31 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 90 (Polychromatic418967fa.accept_21_12_10_6_1_1191
  12 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 90 (accept_3_5 11 31
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 90
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 31 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 90 (accept_3_5 8 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 31 90 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 31 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 90 (Polychromatic418967fa.accept_13_6_5_12_1_307 6 31 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 90 (accept_3_5 5 31 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 90 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 31 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 90
  (Polychromatic418967fa.accept_20_3_11_10_1_3545 3 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 90 (accept_3_5 2 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 90))))))))))))))))))))))))))))))) (allB_succ 30 90 (allA_succ_of_accept 29 30 90
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 30 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 90 2 14 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 30 90 3 9 10 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 30 90 2 13 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 30 90 5 5 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 30 90 6 4 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 90 (Polychromatic418967fa.accept_16_7_14_10_1_3544 23 30 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 90 2 11 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 30 90 3 7 10 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 90 10 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 90 (Polychromatic418967fa.accept_23_19_7_21_1_3543 19 30 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 90 6 3 5 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 90
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 30 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 30 90 2 8 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 30 90 15 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 30 90 2 7 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 30 90 (Polychromatic418967fa.accept_16_13_14_10_1_1669 13 30 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 90 6 2 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 90 10 1 3 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 90 3 3 10 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 90 2 4 15 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 90
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 30 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 30 90 6 1 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 30 90 5 1 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 30 90 2 2 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 90 3 1 10 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 90 2 1 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 30 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 90)))))))))))))))))))))))))))))) (allB_succ 29 90 (allA_succ_of_accept 28
  29 90 (accept_3_4 28 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 90 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 29 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 90 (accept_3_4 25 29 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 90 (Polychromatic418967fa.accept_17_7_12_5_1_1580 24 29 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 90 (accept_3_4 22 29 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 90 (Polychromatic418967fa.accept_14_7_1_6_1_3514
  21 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 90
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 90 (accept_3_4 19 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29
  90 (Polychromatic418967fa.accept_19_18_10_14_1_2392 18 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 90 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 29 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 90 (accept_3_4 16 29 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 90
  (Polychromatic418967fa.accept_16_14_13_10_1_2624 14 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 90 (accept_3_4 13 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29
  90 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 29 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 90 (accept_3_4 10 29 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 29 90 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 29 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 90 (Polychromatic418967fa.accept_17_8_12_5_1_1577 8
  29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 90 (accept_3_4 7 29 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 90 (Polychromatic418967fa.accept_19_6_10_14_1_3542
  6 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 90
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 90 (accept_3_4 4 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 90 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 29 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 90 (accept_3_4 1 29 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 90))))))))))))))))))))))))))))) (allB_succ 28 90 (allA_succ_of_accept 27 28 90
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 28 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 90 2 13 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 90 (Polychromatic418967fa.accept_19_6_9_14_1_3541 25 28 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 90 2 12 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 90 (accept_3_5 23 28 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 90 2 11 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 28 90 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 28 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 90 2 10 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 90 (Polychromatic418967fa.accept_13_6_2_12_1_2802
  19 28 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 90 2 9 14 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 90 (accept_3_5 17 28
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 90 2 8 14 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28 90
  (Polychromatic418967fa.accept_11_4_6_2_1_51 15 28 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 90 2 7 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 90 (Polychromatic418967fa.accept_16_13_12_10_1_3540 13 28 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 90 2 6 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 90 (accept_3_5 11 28 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 28 90 2 5 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 28 90 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 28 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 90 2 4 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 90 (Polychromatic418967fa.accept_17_7_11_5_1_3539 7
  28 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 90 2 3 14 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 90 (accept_3_5 5 28
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 90 2 2 14 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 90
  (Polychromatic418967fa.accept_12_3_4_6_1_434 3 28 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 90 2 1 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 90 (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 28 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 90)))))))))))))))))))))))))))) (allB_succ 27 90 (allA_succ_of_accept 26
  27 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 27 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 90 3 8 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 90 (Polychromatic418967fa.accept_19_4_8_14_1_3538
  23 27 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 90
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 27 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 90 3 7 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 90 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 27 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 90 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 27 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 90 9 2 3 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 90 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 27 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 90 3 5 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 27 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 90 3 4 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 90 (Polychromatic418967fa.accept_13_11_1_12_1_742 11 27 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 90 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 27 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 90 9 1 3 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 90
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 27 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 90 (Polychromatic418967fa.accept_14_7_13_6_1_1177 7 27 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 90 3 2 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 90
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 27 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 90 3 1 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 27 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 90))))))))))))))))))))))))))) (allB_succ 26
  90 (allA_succ_of_accept 25 26 90 (accept_3_4 25 26 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  90 2 12 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 90 (Polychromatic418967fa.accept_19_4_7_14_1_3537 23 26 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 90 2 11 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 26 90 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 26 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 90 2 10 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 90 (accept_3_4 19 26 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 90 2 9 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 26 90 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 26 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 90 2 8 13 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 90
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 26 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 90 2 7 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 90 (accept_3_4 13 26 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 90
  2 6 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26
  90 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 26 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 26 90 2 5 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 26 90 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 26 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 90 2 4 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 90 (accept_3_4 7 26 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 26 90 2 3 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 26 90 (Polychromatic418967fa.accept_20_5_6_10_1_3536 5 26 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 90 2 2 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 90 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 26
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 90 2 1 13 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 90 (accept_3_4 1 26
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 90)))))))))))))))))))))))))) (allB_succ 25 90
  (allA_succ_of_accept 24 25 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 90 (accept_3_5 23 25 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 90 (Polychromatic418967fa.accept_20_2_5_10_1_3535 22 25 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 90 (Polychromatic418967fa.accept_20_1_5_10_1_3534
  21 25 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 90 5 4 5 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 90 (Polychromatic418967fa.accept_20_18_5_10_1_3533 18 25 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 90 (accept_3_5 17 25 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 90 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 25 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 25 90 5 3 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 25 90 (accept_3_5 14 25 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 90 (Polychromatic418967fa.accept_17_13_8_5_1_3532 13 25 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 90
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 90 (accept_3_5 11 25 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 90
  5 2 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25 90
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 25 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 90 (accept_3_5 8 25 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 90 (Polychromatic418967fa.accept_20_6_5_10_1_3531 6 25 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 25 90 5 1 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 25 90 (Polychromatic418967fa.accept_20_4_5_10_1_2308 4 25 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 90 (accept_3_5 2 25 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 90
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 25 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 90))))))))))))))))))))))))) (allB_succ 24 90 (allA_succ_of_accept 23 24 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 90 2 11 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 24 90 3 7 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 24 90 2 10 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 90 (Polychromatic418967fa.accept_21_19_3_6_1_2281 19 24 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 90 6 3 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 90 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 24 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 90 2 8 12 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 24 90 3 5 8 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 24 90 2 7 12 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 90
  (Polychromatic418967fa.accept_19_13_5_14_1_3530 13 24 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 90 6 2 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 90 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 90 2 5 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 90 3 3 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 90 2 4 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 90 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 24 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 90 6 1 4 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 90
  (Polychromatic418967fa.accept_20_5_4_10_1_3529 5 24 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 90 2 2 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 24 90 3 1 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 24 90 2 1 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 90 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 24 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 90)))))))))))))))))))))))) (allB_succ 23 90 (allA_succ_of_accept 22 23 90
  (accept_3_4 22 23 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 90 (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 23 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 90 (accept_3_4 19 23 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 90 (accept_3_4 16 23 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  23 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 90
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 23 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 90 (accept_3_4 13 23 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  90 (Polychromatic418967fa.accept_20_12_3_10_1_3528 12 23 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 90 (accept_3_4 10 23 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 90
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 90 (accept_3_4 7 23 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 90
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 23 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 90 (accept_3_4 4 23 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 23 90 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 23 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 90 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 23 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 90 (accept_3_4 1 23 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 23 90))))))))))))))))))))))) (allB_succ 22 90 (allA_succ_of_accept 21 22 90
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 22 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 90 2 10 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 90 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 22 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 90 2 9 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 90 (accept_3_5 17 22 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 90 2 8 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 90 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 22 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 90 2 7 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 90 (Polychromatic418967fa.accept_20_13_2_10_1_2301
  13 22 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 90 2 6 11 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 90 (accept_3_5 11 22
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 90 2 5 11 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 90
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 22 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 90 2 4 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 90 (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 22 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 90 2 3 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 90 (accept_3_5 5 22 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 90 2 2 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 90 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 22 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 90 2 1 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 90 (Polychromatic418967fa.accept_23_1_22_21_1_3527 1
  22 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 90)))))))))))))))))))))) (allB_succ 21
  90 (allA_succ_of_accept 20 21 90 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 21 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 90 3 6 7 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 90
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 21 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 90 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 21 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 90 3 5 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 90 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 21 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 90
  (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 21 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 90 3 4 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 90 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 21 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 90 3 3 7 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 90
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 21 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 90 3 2 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 90 (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 21 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 90
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 21 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 90 3 1 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 90 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 21 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 90 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 21 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 90))))))))))))))))))))) (allB_succ 20 90
  (allA_succ_of_accept 19 20 90 (accept_3_4 19 20 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 90
  2 9 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20
  90 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 20 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 20 90 2 8 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 20 90 5 3 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 20 90 2 7 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 20 90 (accept_3_4 13 20 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 20 90 2 6 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 20 90 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 20 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 90 10 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 90 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 20 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 90 2 4 10 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 90 (accept_3_4 7 20 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 90 2 3 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 20 90 5 1 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 20 90 2 2 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 20 90 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 20 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 90 2 1 10 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 90 (accept_3_4 1 20 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 20 90)))))))))))))))))))) (allB_succ 19 90 (allA_succ_of_accept 18 19 90
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 19 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 90 (accept_3_5 17 19 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19
  90 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 19 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 19 90 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 19 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 90 (accept_3_5 14 19 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 19 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 90 (Polychromatic418967fa.accept_16_12_3_10_1_3524
  12 19 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 90 (accept_3_5 11 19
  90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 90
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 19 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 19 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 90 (accept_3_5 8 19 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 19 90 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 19 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 90 (Polychromatic418967fa.accept_20_6_19_10_1_3523 6 19 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 90 (accept_3_5 5 19 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 90 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 19 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 90
  (Polychromatic418967fa.accept_17_3_2_5_1_2556 3 19 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 90 (accept_3_5 2 19 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 90
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 19 90))))))))))))))))))) (allB_succ 18 90 (allA_succ_of_accept 17 18 90
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 18 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 90 2 8 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 18 90 3 5 6 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 18 90 2 7 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 90 (Polychromatic418967fa.accept_19_13_18_14_1_3522 13 18 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 90 6 2 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 90 (Polychromatic418967fa.accept_21_11_18_6_1_3521 11 18 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 90 2 5 9 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 18 90 9 1 2 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 18 90 2 4 9 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 90
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 18 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 90 6 1 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 90 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 18 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 90 2 2 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 90 3 1 6 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 90 2 1 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 90 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 18 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 90)))))))))))))))))) (allB_succ 17 90
  (allA_succ_of_accept 16 17 90 (accept_3_4 16 17 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17
  90 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 90 (Polychromatic418967fa.accept_25_14_17_15_1_3520 14 17 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 90 (accept_3_4 13 17 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 90 (Polychromatic418967fa.accept_19_12_17_14_1_3519 12 17 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 90 (accept_3_4 10 17 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17
  90 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 17 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 90 (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 17 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 90 (accept_3_4 7 17 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 90 (Polychromatic418967fa.accept_22_6_17_2_1_3518 6 17 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 90 (Polychromatic418967fa.accept_13_5_4_12_1_2058 5
  17 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 90 (accept_3_4 4 17 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 17 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 90 (accept_3_4 1 17 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  90))))))))))))))))) (allB_succ 16 90 (allA_succ_of_accept 15 16 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 16 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 16 90 2 7 8 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 16 90
  (Polychromatic418967fa.accept_19_13_16_14_1_3517 13 16 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 16 90 2 6 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 16 90 (accept_3_5 11 16 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16 90
  2 5 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 16 90
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 16 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 16 90 2 4 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 16 90 (Polychromatic418967fa.accept_21_7_16_6_1_3516 7 16 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 90 2 3 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 90 (accept_3_5 5 16 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 16 90 2 2 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 16 90 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 16 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 90 2 1 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 16
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 90)))))))))))))))) (allB_succ 15 90
  (allA_succ_of_accept 14 15 90 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 15 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 90 3 4 5 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 90
  (Polychromatic418967fa.accept_16_11_15_10_1_3515 11 15 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 15 90 5 2 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 15 90 3 3 5 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 90 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 15 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 90 (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 15 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 90 3 2 5 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 15 90 5 1 3 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 90
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 15 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 15 90 3 1 5 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 15 90 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 15 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 90))))))))))))))) (allB_succ 14 90
  (allA_succ_of_accept 13 14 90 (accept_3_4 13 14 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 90
  2 6 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 90
  (Polychromatic418967fa.accept_13_11_1_12_1_742 11 14 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 90 2 5 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 90 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 14 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 90 2 4 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 90 (accept_3_4 7 14 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 90 2 3 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 90 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 14 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 90 2 2 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 90 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 14
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 90 2 1 7 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 90 (accept_3_4 1 14 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 14 90)))))))))))))) (allB_succ 13 90 (allA_succ_of_accept 12 13 90
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 13 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 90 (accept_3_5 11 13 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  90 (Polychromatic418967fa.accept_17_10_13_5_1_3513 10 13 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 90 (Polychromatic418967fa.accept_17_9_13_5_1_3512 9 13 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 90 (accept_3_5 8 13 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 90 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 90 (Polychromatic418967fa.accept_23_6_13_21_1_3511
  6 13 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 90 (accept_3_5 5 13 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 90 (Polychromatic418967fa.accept_19_4_13_14_1_3510
  4 13 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 90 (accept_3_5 2 13 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 90
  (Polychromatic418967fa.accept_19_1_13_14_1_3509 1 13 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 90))))))))))))) (allB_succ 12 90 (allA_succ_of_accept 11 12 90
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 90 2 5 6 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 12 90 3 3 4 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 12 90 2 4 6 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 90 (Polychromatic418967fa.accept_17_7_12_5_1_1580 7 12 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 90 6 1 2 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 90 (Polychromatic418967fa.accept_16_5_12_10_1_3508 5 12 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 90 2 2 6 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 90 3 1 4 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 90 2 1 6 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 90
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 90)))))))))))) (allB_succ 11 90 (allA_succ_of_accept 10 11 90 (accept_3_4 10 11 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 90
  (Polychromatic418967fa.accept_22_8_11_2_1_3507 8 11 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 90 (accept_3_4 7 11 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 90
  (Polychromatic418967fa.accept_17_6_11_5_1_3506 6 11 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 90 (accept_3_4 4 11 90 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 11 90 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 11 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 90 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 11 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 90 (accept_3_4 1 11 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 11 90))))))))))) (allB_succ 10 90 (allA_succ_of_accept 9 10 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 10 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 90 2 4 5 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 90 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 10 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 90 2 3 5 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 10 90 5 1 2 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 10 90 2 2 5 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 90 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 10 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 90 2 1 5 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 90
  (Polychromatic418967fa.accept_11_1_10_2_1_58 1 10 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 90)))))))))) (allB_succ 9 90 (allA_succ_of_accept 8 9 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 9 90 3 2 3 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 9 90 (Polychromatic418967fa.accept_19_5_9_14_1_3505 5 9 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 90 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 9 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 90 3 1 3 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 90
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 9 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 90 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 9 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 9 90))))))))) (allB_succ 8 90 (allA_succ_of_accept 7 8 90 (accept_3_4 7 8 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 90 2 3 4 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 90 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 90 2 2 4 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 90
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 8 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 8 90 2 1 4 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 8 90 (accept_3_4 1 8 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 90))))))))
  (allB_succ 7 90 (allA_succ_of_accept 6 7 90 (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 7 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 90 (accept_3_5 5 7 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 7 90 (Polychromatic418967fa.accept_13_4_7_12_1_2823 4 7 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 90 (Polychromatic418967fa.accept_16_3_7_10_1_3503 3
  7 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 90 (accept_3_5 2 7 90
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 90))))))) (allB_succ 6 90
  (allA_succ_of_accept 5 6 90 (Polychromatic418967fa.accept_13_5_6_12_1_2750 5 6 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 90 2 2 3 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 6 90 3 1 2 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 6 90 2 1 3 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 90 (Polychromatic418967fa.accept_17_1_6_5_1_3502 1 6 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 90)))))) (allB_succ 5 90 (allA_succ_of_accept
  4 5 90 (accept_3_4 4 5 90 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 90
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 90 (Polychromatic418967fa.accept_13_2_5_12_1_2043 2 5 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 90 (accept_3_4 1 5 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 90))))) (allB_succ 4 90 (allA_succ_of_accept 3 4 90
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 4 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 4 90 2 1 2 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 4 90 (Polychromatic418967fa.accept_17_1_4_5_1_3501 1 4 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 4 90)))) (allB_succ 3 90 (allA_succ_of_accept 2 3 90
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 90 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 3 90))) (allB_succ 2 90 (allA_succ_of_accept 1 2 90 (accept_3_4 1 2 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 2 90)) (allB_two
  90))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


