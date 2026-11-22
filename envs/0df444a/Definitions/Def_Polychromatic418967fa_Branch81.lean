-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch81
-- name    : Polychromatic418967fa_Branch81
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:09.325163+00:00
-- url     : https://prove2.me/theorems/057697b4-73e5-4108-a1e9-5687475f7de1
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

def Polychromatic418967fa.branch_81 : allB 81 81 :=
  allB_succ' 2 80 81 (Eq.refl Bool.true) (allA_succ_of_accept 1 80 81 (accept_3_4 1 80 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 81)) (allB_succ' 3 79 81 (Eq.refl Bool.true) (allA_succ_of_accept 2 79 81 (accept_3_5 2 79 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 81 (Polychromatic418967fa.accept_19_1_3_5_1_3092 1
  79 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 81))) (allB_succ' 4 78 81 (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 78 81 3 1 26 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 2 78 81 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 78 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 81 (Polychromatic418967fa.accept_15_1_3_6_1_621 1
  78 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 81)))) (allB_succ' 5 77 81 (Eq.refl
  Bool.true) (allA_succ_of_accept 4 77 81 (accept_3_4 4 77 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 77 81 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 77 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 81 (accept_3_4 1 77 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 77 81))))) (allB_succ' 6 76 81 (Eq.refl Bool.true) (allA_succ_of_accept 5 76
  81 (accept_3_5 5 76 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76 81
  (Polychromatic418967fa.accept_16_4_12_1_1_1204 4 76 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 81 (accept_3_5 2 76 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 81)))))) (allB_succ' 7 75 81 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 75 81 3 2 25 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 75 81 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 75 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 81 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 75 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 81 3 1 25 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 75 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75 81))))))) (allB_succ' 8 74 81 (Eq.refl Bool.true) (allA_succ_of_accept 7
  74 81 (accept_3_4 7 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 81
  (Polychromatic418967fa.accept_12_6_2_9_1_537 6 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 81 (accept_3_4 4 74 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 81 (Polychromatic418967fa.accept_13_2_9_3_1_2212 2
  74 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 81 (accept_3_4 1 74 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 81)))))))) (allB_succ' 9 73 81 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 73 81 (accept_3_5 8 73 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 81
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 73 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 73 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 81 (accept_3_5 5 73 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 81 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3
  73 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 81 (accept_3_5 2 73 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 81))))))))) (allB_succ' 10 72 81 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 72 81 9 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 72 81 (Polychromatic418967fa.accept_13_8_7_3_1_430 8 72 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 81 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7
  72 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 81 3 2 24 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 81
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 81 (Polychromatic418967fa.accept_13_4_7_3_1_92 4 72 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 81 3 1 24 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 81 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 72 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 81
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 72 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 81)))))))))) (allB_succ' 11 71 81 (Eq.refl Bool.true) (allA_succ_of_accept 10 71 81 (accept_3_4 10 71 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 81 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9
  71 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 81
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 81 (accept_3_4 7 71 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 81 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 81 (accept_3_4 4 71 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 81 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 71 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 81 (accept_3_4 1 71 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 81))))))))))) (allB_succ' 12 70 81 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 81 (accept_3_5 11 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 70
  81 (Polychromatic418967fa.accept_19_10_13_5_1_3091 10 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 81 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 70 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 81 (accept_3_5 8 70 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 70 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 81 (Polychromatic418967fa.accept_12_6_10_9_1_531 6
  70 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 81 (accept_3_5 5 70 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 81 (Polychromatic418967fa.accept_15_4_10_6_1_2997 4
  70 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 81 (accept_3_5 2 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 81
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 81)))))))))))) (allB_succ' 13 69 81 (Eq.refl Bool.true) (allA_succ_of_gcd 12 69 81 3 4 23 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 81
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 69 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 69 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 81 3 3 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 81 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 69 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 81
  (Polychromatic418967fa.accept_11_7_3_4_1_729 7 69 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 81 3 2 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 81 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 81 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 69 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 81 3 1 23 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 81
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 69 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 81 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 69 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 81))))))))))))) (allB_succ' 14 68 81 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 81 (accept_3_4 13 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68
  81 (Polychromatic418967fa.accept_16_12_4_1_1_1257 12 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 81 (accept_3_4 10 68 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 68 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 81
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 81 (accept_3_4 7 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 81
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 81 (accept_3_4 4 68 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 81 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 68 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 68
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 81 (accept_3_4 1 68 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 81)))))))))))))) (allB_succ' 15 67 81 (Eq.refl Bool.true)
  (allA_succ_of_accept 14 67 81 (accept_3_5 14 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67
  81 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 67 81 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 67 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 81 (accept_3_5 11 67 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 67 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 81 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9
  67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 81 (accept_3_5 8 67 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 81 (Polychromatic418967fa.accept_19_7_10_5_1_3090 7
  67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 81 (accept_3_5 5 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 81
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 81 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 67 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 81 (accept_3_5 2 67 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 81 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 67 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 81))))))))))))))) (allB_succ' 16 66 81 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 66 81 3 5 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 81 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 66 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 66 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 81 3 4 22 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 81 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 66 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 81 3 3 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 66 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 81 3 2 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 81 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 66 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 81 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 66 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 81 3 1 22 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 81
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 66 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 66 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 81)))))))))))))))) (allB_succ' 17 65 81 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 65 81 (accept_3_4 16 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 65
  81 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 65 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 81 (accept_3_4 13 65 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 65 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 81 (Polychromatic418967fa.accept_15_11_5_6_1_669
  11 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 81 (accept_3_4 10 65
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 81 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  9 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 81
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 81 (accept_3_4 7 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 81
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 81 (accept_3_4 4 65 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 81 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 65 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 81 (accept_3_4 1 65 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 81))))))))))))))))) (allB_succ' 18 64 81 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 81 (accept_3_5 17 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64
  81 (Polychromatic418967fa.accept_25_16_14_6_1_3089 16 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 81 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 64 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 81 (accept_3_5 14 64 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 81
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 81 (accept_3_5 11 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64
  81 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 64 81 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 64 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 81 (accept_3_5 8 64 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 64 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 81 (Polychromatic418967fa.accept_12_6_4_9_1_544 6
  64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 81 (accept_3_5 5 64 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 81 (Polychromatic418967fa.accept_13_4_12_3_1_2999 4
  64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 81
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 81 (accept_3_5 2 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 81
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 81)))))))))))))))))) (allB_succ' 19 63 81 (Eq.refl Bool.true) (allA_succ_of_gcd 18 63 81 9 2 7 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 81
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 81 (Polychromatic418967fa.accept_15_1_3_6_1_621 16 63 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 81 3 5 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 81
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 81 3 4 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 81 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 81 9 1 7 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 81
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 81 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 63 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 81 3 2 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 81 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 63 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 81
  (Polychromatic418967fa.accept_14_4_7_11_1_790 4 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 81 3 1 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 81 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 63 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 81))))))))))))))))))) (allB_succ' 20 62 81 (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 81 (accept_3_4 19 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 62 81 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 62 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 81 (accept_3_4 16 62 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 81
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 81 (accept_3_4 13 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 62
  81 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 62 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 81 (accept_3_4 10 62 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 62 81 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 62 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 81 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8
  62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 81 (accept_3_4 7 62 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 81 (Polychromatic418967fa.accept_10_6_2_1_1_494 6
  62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 81
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 81 (accept_3_4 4 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 81 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 62 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 81 (accept_3_4 1 62 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 81)))))))))))))))))))) (allB_succ' 21 61 81 (Eq.refl Bool.true) (allA_succ_of_accept 20 61 81
  (accept_3_5 20 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 81
  (Polychromatic418967fa.accept_13_6_9_3_1_915 19 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 61 81 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 61 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 81 (accept_3_5 17 61 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 61 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 81 (accept_3_5 14 61 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 81 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 81
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 81 (accept_3_5 11 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61
  81 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 61 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 61 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 81 (accept_3_5 8 61 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 61 81 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 61 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 81 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 61
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 81 (accept_3_5 5 61 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 81
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 81 (accept_3_5 2 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 81
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 61 81))))))))))))))))))))) (allB_succ' 22 60 81 (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 81 3 7 20 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 60 81
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 60 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 60 81 (Polychromatic418967fa.accept_18_1_6_9_1_2001 19 60 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 81 3 6 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 81 (Polychromatic418967fa.accept_19_17_3_5_1_3088 17 60 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 81
  (Polychromatic418967fa.accept_17_16_9_13_1_3087 16 60 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 60 81 3 5 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 60 81 (Polychromatic418967fa.accept_18_14_6_9_1_1950 14 60 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 81 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 60 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 81 3 4 20 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 81
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 60 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 81 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 60 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 81 3 3 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 81 (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 60 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 81
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 60 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 81 3 2 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 81 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 60 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 81 (Polychromatic418967fa.accept_16_4_12_1_1_1204 4 60 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 81 3 1 20 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 81
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 2 60 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 81 (Polychromatic418967fa.accept_14_1_4_11_1_3036 1 60 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 81)))))))))))))))))))))) (allB_succ' 23 59 81 (Eq.refl Bool.true)
  (allA_succ_of_accept 22 59 81 (accept_3_4 22 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59
  81 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 59 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 81 (accept_3_4 19 59 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 59 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 81 (Polychromatic418967fa.accept_13_4_7_3_1_92 17
  59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 81 (accept_3_4 16 59 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 81 (accept_3_4 13 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59
  81 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 59 81 (Polychromatic418967fa.accept_13_11_7_3_1_894 11 59 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 81 (accept_3_4 10 59 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 59 81 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 59 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 81 (accept_3_4 7 59 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 81
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 81 (accept_3_4 4 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 81
  (Polychromatic418967fa.accept_12_3_11_9_1_193 3 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 81 (accept_3_4 1 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 59 81))))))))))))))))))))))) (allB_succ' 24 58 81 (Eq.refl Bool.true) (allA_succ_of_accept 23 58 81
  (accept_3_5 23 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 81
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 22 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 58 81 (Polychromatic418967fa.accept_22_21_14_15_1_3085 21 58 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 81 (accept_3_5 20 58 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 58 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 81 (Polychromatic418967fa.accept_11_7_3_4_1_729 18
  58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 81 (accept_3_5 17 58 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 81 (Polychromatic418967fa.accept_19_16_1_5_1_3084
  16 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 81 (accept_3_5 14 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 58
  81 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 58 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 58 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 81 (accept_3_5 11 58 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 58 81 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 58 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 81 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9
  58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 81 (accept_3_5 8 58 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 81
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 81 (accept_3_5 5 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 81
  (Polychromatic418967fa.accept_15_4_13_6_1_642 4 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 81 (accept_3_5 2 58 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 81)))))))))))))))))))))))) (allB_succ' 25 57 81 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 57 81 3 8 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 57 81 (Polychromatic418967fa.accept_21_2_15_18_1_806 23 57 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 81 (Polychromatic418967fa.accept_13_9_5_3_1_428 22
  57 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 81 3 7 19 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 81
  (Polychromatic418967fa.accept_11_9_2_4_1_707 20 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 81 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 57 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 81 3 6 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 81 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 81
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 81 3 5 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 81 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 57 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 81 (Polychromatic418967fa.accept_16_13_9_1_1_3022 13 57 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 81 3 4 19 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 81
  (Polychromatic418967fa.accept_13_11_5_3_1_889 11 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 81 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 57 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 81 3 3 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 81 (Polychromatic418967fa.accept_13_8_5_3_1_427 8 57 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 81
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 81 3 2 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 81 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 81 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 57 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 81 3 1 19 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 81
  (Polychromatic418967fa.accept_13_2_5_3_1_406 2 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 81 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 57 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 81))))))))))))))))))))))))) (allB_succ' 26 56 81 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 56 81 (accept_3_4 25 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56
  81 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 56 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 81 (accept_3_4 22 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 56 81 (Polychromatic418967fa.accept_18_3_2_9_1_1013 21 56 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 81 (Polychromatic418967fa.accept_13_7_4_3_1_3064
  20 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 81 (accept_3_4 19 56
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 81 (Polychromatic418967fa.accept_12_6_8_9_1_553
  18 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 81
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 56 81 (accept_3_4 16 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56
  81 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 56 81 (Polychromatic418967fa.accept_13_1_4_3_1_1545 14 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 81 (accept_3_4 13 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 56 81 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 56 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 81 (accept_3_4 10 56 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 81 (Polychromatic418967fa.accept_15_9_11_6_1_637 9
  56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 81
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 81 (accept_3_4 7 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56 81
  (Polychromatic418967fa.accept_12_6_8_9_1_553 6 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 81 (accept_3_4 4 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 81 (Polychromatic418967fa.accept_15_3_11_6_1_3083 3 56 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 81 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 81 (accept_3_4 1 56 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 81)))))))))))))))))))))))))) (allB_succ' 27 55 81 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 55 81 (accept_3_5 26 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 55 81 (Polychromatic418967fa.accept_17_8_4_13_1_3014 25 55 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 81 (accept_3_5 23 55 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 81
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 21 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 81 (accept_3_5 20 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55
  81 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 81 (accept_3_5 17 55 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 81 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  15 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 81 (accept_3_5 14 55
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 81
  (Polychromatic418967fa.accept_31_13_24_19_1_3082 13 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 55 81 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 81 (accept_3_5 11 55 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 55 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 81 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 55
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 81 (accept_3_5 8 55 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 81 (Polychromatic418967fa.accept_19_7_17_5_1_3081 7
  55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 81 (accept_3_5 5 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 81
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 55 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 81 (accept_3_5 2 55 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 81 (Polychromatic418967fa.accept_15_1_10_6_1_631 1 55 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 81))))))))))))))))))))))))))) (allB_succ' 28 54 81 (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 54 81 27 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 26 54 81 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 54 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 81 (Polychromatic418967fa.accept_10_5_4_1_1_842 25
  54 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 81 3 8 18 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 54 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 81 3 7 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 81 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 54 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 81 9 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 81 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 54 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 54 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 81 3 5 18 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 81
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 81 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 54 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 81 3 4 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 81
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 54 81 9 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 54 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 54 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 81 3 2 18 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 81
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 81 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 54 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 81 3 1 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 54 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 81
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 81)))))))))))))))))))))))))))) (allB_succ' 29 53 81 (Eq.refl Bool.true) (allA_succ_of_accept 28 53 81
  (accept_3_4 28 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 81
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 53 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 81 (accept_3_4 25 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 53 81 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 53 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 81 (Polychromatic418967fa.accept_17_6_2_13_1_3051
  23 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 81 (accept_3_4 22 53
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 81
  (Polychromatic418967fa.accept_25_21_3_6_1_3080 21 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 53 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 81 (accept_3_4 19 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 53 81 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 53 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 81 (Polychromatic418967fa.accept_13_4_1_3_1_3058
  17 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 81 (accept_3_4 16 53
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 81 (Polychromatic418967fa.accept_12_3_5_9_1_176
  15 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 81
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 81 (accept_3_4 13 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53
  81 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 53 81 (Polychromatic418967fa.accept_13_11_1_3_1_910 11 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 81 (accept_3_4 10 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 53 81 (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 53 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 81 (accept_3_4 7 53 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 81 (Polychromatic418967fa.accept_13_6_1_3_1_1522 6
  53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 81
  (Polychromatic418967fa.accept_13_5_1_3_1_878 5 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 81 (accept_3_4 4 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 81
  (Polychromatic418967fa.accept_12_3_5_9_1_176 3 53 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 81 (accept_3_4 1 53 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 81))))))))))))))))))))))))))))) (allB_succ' 30 52 81 (Eq.refl Bool.true) (allA_succ_of_accept
  29 52 81 (accept_3_5 29 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 81
  (Polychromatic418967fa.accept_15_13_7_6_1_682 28 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 52 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 81 (accept_3_5 26 52 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 52 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 81 (Polychromatic418967fa.accept_16_8_4_1_1_2102
  24 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 81 (accept_3_5 23 52
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 81 (Polychromatic418967fa.accept_7_1_3_4_1_128
  22 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 81
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 81 (accept_3_5 20 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 52
  81 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 52 81 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 52 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 81 (accept_3_5 17 52 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 52 81 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 52 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 81 (accept_3_5 14 52 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 81
  (Polychromatic418967fa.accept_11_1_8_4_1_717 12 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 81 (accept_3_5 11 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 52
  81 (Polychromatic418967fa.accept_19_10_14_5_1_3079 10 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 81 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 52 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 81 (accept_3_5 8 52 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 52 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 52
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 81 (accept_3_5 5 52 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52 81 (Polychromatic418967fa.accept_22_4_8_15_1_3078 4
  52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 81
  (Polychromatic418967fa.accept_10_3_2_1_1_839 3 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 52 81 (accept_3_5 2 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 81
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 81)))))))))))))))))))))))))))))) (allB_succ' 31 51 81 (Eq.refl Bool.true) (allA_succ_of_gcd 30 51 81 3 10
  17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 81
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 81 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 51 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 81 3 9 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 81
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 51 81 3 8 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 51 81 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 51 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 81 3 7 17 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 81
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 51 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 81 3 6 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 81 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 51 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 81
  (Polychromatic418967fa.accept_14_2_9_11_1_3054 16 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 81 3 5 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 81 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 51 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 81 3 4 17 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 81
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 81 3 3 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 81 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 51 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 81
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 81 3 2 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 51 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 81 (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 51 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 81 3 1 17 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 81 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 51 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 81))))))))))))))))))))))))))))))) (allB_succ' 32 50 81 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 81 (accept_3_4 31 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 50 81 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 50 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 81 (accept_3_4 28 50 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 81
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 81 (accept_3_4 25 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 50
  81 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 50 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 81 (accept_3_4 22 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 50 81 (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 50 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 81 (Polychromatic418967fa.accept_13_7_11_3_1_1540
  20 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 50 81 (accept_3_4 19 50
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 81 (Polychromatic418967fa.accept_12_6_2_9_1_537
  18 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 50 81
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 50 81 (accept_3_4 16 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 50
  81 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 50 81 (Polychromatic418967fa.accept_13_1_11_3_1_901 14 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 81 (accept_3_4 13 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 50 81 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 50 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 81 (accept_3_4 10 50 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 81 (Polychromatic418967fa.accept_16_9_2_1_1_3077 9
  50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 81
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 81 (accept_3_4 7 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 81
  (Polychromatic418967fa.accept_12_6_2_9_1_537 6 50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 81 (accept_3_4 4 50 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 81 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2
  50 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 81 (accept_3_4 1 50 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 81)))))))))))))))))))))))))))))))) (allB_succ' 33 49 81 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 49 81 (accept_3_5 32 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 49 81 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 81 (Polychromatic418967fa.accept_20_10_9_1_1_3076 30 49 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 81 (accept_3_5 29 49 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 81
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 81 (accept_3_5 26 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49
  81 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 49 81 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 81 (accept_3_5 23 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 49 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 81 (Polychromatic418967fa.accept_11_10_5_4_1_711
  21 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 81 (accept_3_5 20 49
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 81
  (Polychromatic418967fa.accept_13_6_10_3_1_897 19 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 81 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 81 (accept_3_5 17 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 81 (Polychromatic418967fa.accept_10_5_9_1_1_187 15
  49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 81 (accept_3_5 14 49 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 81 (Polychromatic418967fa.accept_15_13_4_6_1_3046
  13 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 81
  (Polychromatic418967fa.accept_10_2_9_1_1_185 12 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 81 (accept_3_5 11 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49
  81 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 49 81 (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 81 (accept_3_5 8 49 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 49 81 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 49 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 81 (Polychromatic418967fa.accept_13_6_10_3_1_897 6
  49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 81 (accept_3_5 5 49 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 81
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 81 (accept_3_5 2 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 81
  (Polychromatic418967fa.accept_22_1_5_15_1_3074 1 49 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 81))))))))))))))))))))))))))))))))) (allB_succ' 34 48 81 (Eq.refl Bool.true) (allA_succ_of_gcd 33 48 81 3
  11 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 81
  (Polychromatic418967fa.accept_13_6_9_3_1_915 32 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 48 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 81 3 10 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 81 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 48 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 81
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 28 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 48 81 3 9 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 48 81 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 48 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 81 (Polychromatic418967fa.accept_13_12_9_3_1_3047 25 48 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 81 3 8 16 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 81
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 81 (Polychromatic418967fa.accept_18_4_12_9_1_2011 22 48 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 81 3 7 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 81 (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 48 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 81
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 81 3 6 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 81 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 48 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 81 3 5 16 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 81
  (Polychromatic418967fa.accept_19_14_10_5_1_3073 14 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 81 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 48 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 81 3 4 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 81 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 48 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 81
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 48 81 3 3 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 48 81 (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 48 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 81 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 48 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 81 3 2 16 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 81
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 81 (Polychromatic418967fa.accept_17_4_14_13_1_3072 4 48 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 81 3 1 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 81 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 48 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 81
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 48 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 81)))))))))))))))))))))))))))))))))) (allB_succ' 35 47 81 (Eq.refl Bool.true) (allA_succ_of_accept 34 47
  81 (accept_3_4 34 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 81
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 33 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 81 (accept_3_4 31 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 81 (accept_3_4 28 47 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 81 (Polychromatic418967fa.accept_7_6_5_4_1_297 27
  47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 81 (accept_3_4 25 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47
  81 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 47 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 81 (accept_3_4 22 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 47 81 (Polychromatic418967fa.accept_16_5_15_1_1_2113 21 47 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 81 (accept_3_4 19 47 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 81
  (Polychromatic418967fa.accept_31_17_16_19_1_3071 17 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 81 (accept_3_4 16 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47
  81 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 81 (accept_3_4 13 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 81 (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 47 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 81 (Polychromatic418967fa.accept_13_11_8_3_1_3016
  11 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 81 (accept_3_4 10 47
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 81
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 81 (accept_3_4 7 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 81 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 81 (accept_3_4 4 47 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 81 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 47 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 81 (accept_3_4 1 47 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 81))))))))))))))))))))))))))))))))))) (allB_succ' 36 46 81
  (Eq.refl Bool.true) (allA_succ_of_accept 35 46 81 (accept_3_5 35 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 46 81 (Polychromatic418967fa.accept_13_8_7_3_1_430 34 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 81 (Polychromatic418967fa.accept_15_3_1_6_1_206 33 46 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 81 (accept_3_5 32 46 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 46 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 81
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 46 81 (accept_3_5 29 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46
  81 (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 81 (accept_3_5 26 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 81 (Polychromatic418967fa.accept_13_11_7_3_1_894
  24 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 81 (accept_3_5 23 46
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 81
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 81 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 81 (accept_3_5 20 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 81 (Polychromatic418967fa.accept_12_6_10_9_1_531
  18 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 81 (accept_3_5 17 46
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 81
  (Polychromatic418967fa.accept_17_16_12_13_1_3070 16 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 46 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 81 (accept_3_5 14 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 46 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 81 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  12 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 81 (accept_3_5 11 46
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 81
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 10 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 46 81 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 81 (accept_3_5 8 46 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 46 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 81 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6
  46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 81 (accept_3_5 5 46 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 81 (Polychromatic418967fa.accept_13_4_7_3_1_92 4 46
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 81 (accept_3_5 2 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 81
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 81)))))))))))))))))))))))))))))))))))) (allB_succ' 37 45 81 (Eq.refl Bool.true) (allA_succ_of_gcd 36 45
  81 9 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45
  81 (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 45 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 81 3 11 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 81 (Polychromatic418967fa.accept_17_15_11_13_1_2039 32 45 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 81
  (Polychromatic418967fa.accept_13_5_6_3_1_868 31 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 81 3 10 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 45 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 81 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 45 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 81 9 3 5 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 81
  (Polychromatic418967fa.accept_10_6_5_1_1_482 26 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 81 (Polychromatic418967fa.accept_16_9_13_1_1_3069 25 45 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 81 3 8 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 81 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 45 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 81
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 81 3 7 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 45 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 81 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 45 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 81 9 2 5 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 81
  (Polychromatic418967fa.accept_19_17_7_5_1_1883 17 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 81 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 45 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 81 3 5 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 81 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 45 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 81
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 81 3 4 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 81 (Polychromatic418967fa.accept_21_11_3_18_1_3068 11 45 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 81 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 45 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 81 9 1 5 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 81
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 81 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 45 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 81 3 2 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 81 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 45 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 81
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 45 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 81 3 1 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 81 (Polychromatic418967fa.accept_19_2_7_5_1_3067 2 45 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 45 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 81)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 44 81 (Eq.refl Bool.true) (allA_succ_of_accept 37 44 81 (accept_3_4 37 44 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 81 (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 44 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 44 81
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 44 81 (accept_3_4 34 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 44
  81 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 44 81 (Polychromatic418967fa.accept_13_6_5_3_1_426 32 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 81 (accept_3_4 31 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 44 81 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 44 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 29
  44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 81 (accept_3_4 28 44 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 81 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 81
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 81 (accept_3_4 25 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44
  81 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 81 (accept_3_4 22 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 81 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 44 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 81 (Polychromatic418967fa.accept_7_6_2_4_1_291 20
  44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 81 (accept_3_4 19 44 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 81 (Polychromatic418967fa.accept_12_6_8_9_1_553 18
  44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 81
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 81 (accept_3_4 16 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 44
  81 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 44 81 (Polychromatic418967fa.accept_13_1_5_3_1_888 14 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 81 (accept_3_4 13 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 44 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 44 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 81 (accept_3_4 10 44 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 81 (Polychromatic418967fa.accept_13_9_5_3_1_428 9
  44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 81
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 81 (accept_3_4 7 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 81
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 81 (accept_3_4 4 44 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 81 (Polychromatic418967fa.accept_17_3_10_13_1_2021 3 44 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 81 (Polychromatic418967fa.accept_13_2_5_3_1_406 2
  44 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 81 (accept_3_4 1 44 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 81)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 43 81
  (Eq.refl Bool.true) (allA_succ_of_accept 38 43 81 (accept_3_5 38 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 43 81 (Polychromatic418967fa.accept_15_7_13_6_1_696 37 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 81 (Polychromatic418967fa.accept_21_15_1_18_1_3066 36 43 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 81 (accept_3_5 35 43 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 81
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 81 (accept_3_5 32 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43
  81 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 43 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 81 (accept_3_5 29 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 43 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 81 (Polychromatic418967fa.accept_11_5_10_4_1_1157
  27 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 81 (accept_3_5 26 43
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 81
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 43 81 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 81 (accept_3_5 23 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 43 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 81 (Polychromatic418967fa.accept_17_4_9_13_1_2020
  21 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 81 (accept_3_5 20 43
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 81 (Polychromatic418967fa.accept_7_5_1_4_1_122
  19 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 81 (accept_3_5 17 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43
  81 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 43 81 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 81 (accept_3_5 14 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 43 81 (Polychromatic418967fa.accept_20_13_3_1_1_3065 13 43 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 81 (Polychromatic418967fa.accept_7_5_1_4_1_122 12
  43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 81 (accept_3_5 11 43 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 81
  (Polychromatic418967fa.accept_21_9_1_18_1_1761 9 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 81 (accept_3_5 8 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 81
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 81 (accept_3_5 5 43 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 43 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 81 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 43 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 81 (accept_3_5 2 43 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 81 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 43 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 81)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 42 81 (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 81 3 13 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 81 (Polychromatic418967fa.accept_12_2_6_9_1_19 38
  42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 81
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 81 3 12 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 81 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 42 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 81 3 11 14 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 81
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 81 3 10 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 81 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 42 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 81
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 42 81 3 9 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 42 81 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 81 (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 42 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 81 3 8 14 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 81 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 81 3 7 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 81 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 42 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 81 3 6 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 81 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 81 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 42 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 81 3 5 14 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 42 81
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 81 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 81 3 4 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 81
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 42 81 3 3 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 42 81 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 81 3 2 14 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 81
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 81 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 42 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 81 3 1 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 81 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 42 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 81
  (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 42 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 81)))))))))))))))))))))))))))))))))))))))) (allB_succ 41 81 (allA_succ_of_accept 40 41 81 (accept_3_4 40
  41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 81
  (Polychromatic418967fa.accept_12_3_5_9_1_176 39 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 81 (accept_3_4 37 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 81 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 81 (Polychromatic418967fa.accept_13_9_2_3_1_3027
  35 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 81 (accept_3_4 34 41
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 81 (Polychromatic418967fa.accept_7_5_6_4_1_117
  33 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 81
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 81 (accept_3_4 31 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  81 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 41 81 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 81 (accept_3_4 28 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 41 81 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 26
  41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 81 (accept_3_4 25 41 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 81
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 81 (accept_3_4 22 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41
  81 (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 81 (accept_3_4 19 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 81 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 17
  41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 81 (accept_3_4 16 41 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 81 (Polychromatic418967fa.accept_12_3_5_9_1_176 15
  41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 81
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 81 (accept_3_4 13 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  81 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 41 81 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 81 (accept_3_4 10 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 41 81 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 81 (accept_3_4 7 41 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 81 (Polychromatic418967fa.accept_17_6_7_13_1_3062 6
  41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 81
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 81 (accept_3_4 4 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 81
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 41 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 81 (accept_3_4 1 41 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 81))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 81 (allA_succ_of_accept 39 40 81
  (Polychromatic418967fa.accept_16_7_8_1_1_3061 39 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 81 (accept_3_5 38 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 40
  81 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 40 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 81 (accept_3_5 35 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 40 81 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 40 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 81 (Polychromatic418967fa.accept_13_7_1_3_1_1523
  33 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 81 (accept_3_5 32 40
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 40 81 (Polychromatic418967fa.accept_6_1_4_3_1_14
  31 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 40 81
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 40 81 (accept_3_5 29 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 40
  81 (Polychromatic418967fa.accept_13_2_1_3_1_419 28 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 40 81 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 81 (accept_3_5 26 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 40 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 40 81 (Polychromatic418967fa.accept_13_11_1_3_1_910
  24 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 81 (accept_3_5 23 40
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 81 (Polychromatic418967fa.accept_7_1_5_4_1_134
  22 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 81
  (Polychromatic418967fa.accept_22_21_18_15_1_3060 21 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 81 (accept_3_5 20 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 40
  81 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 40 81 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 81 (accept_3_5 17 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 40 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 40 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 40 81 (accept_3_5 14 40 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 81
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 81 (accept_3_5 11 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40
  81 (Polychromatic418967fa.accept_19_10_2_5_1_3059 10 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 40 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 81 (accept_3_5 8 40 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 40 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 81 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 40
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 81 (accept_3_5 5 40 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 81 (Polychromatic418967fa.accept_13_4_1_3_1_3058 4
  40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 81
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 81 (accept_3_5 2 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 81
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 81)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 81 (allA_succ_of_accept 38 39 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 81 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 39 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 81 3 12 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 81 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 39 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 81 3 11 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 81 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 39 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 81 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 39 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 81 3 10 13 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 81
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 81 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 39 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 81 3 9 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 81
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 81 3 8 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 81 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 39 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 81 3 7 13 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 81
  (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 81 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 39 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 81 3 6 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 81 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 39 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 81
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 81 3 5 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 81 (Polychromatic418967fa.accept_11_2_6_4_1_3028 13 39 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 81 3 4 13 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 81
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 81 3 3 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 81 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 39 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 81
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 81 3 2 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 81 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 39 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 81 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 39 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 81 3 1 13 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 81 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 39 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 81))))))))))))))))))))))))))))))))))))))) (allB_succ 38 81
  (allA_succ_of_accept 37 38 81 (accept_3_4 37 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 38
  81 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 38 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 81 (accept_3_4 34 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 38 81 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 38 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 81 (Polychromatic418967fa.accept_11_10_5_4_1_711
  32 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 38 81 (accept_3_4 31 38
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 38 81 (Polychromatic418967fa.accept_12_6_2_9_1_537
  30 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 38 81
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 38 81 (accept_3_4 28 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 38
  81 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 38 81 (Polychromatic418967fa.accept_17_9_4_13_1_3057 26 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 38 81 (accept_3_4 25 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 38 81 (Polychromatic418967fa.accept_18_6_2_9_1_3056 24 38 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 38 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 81 (accept_3_4 22 38 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 81 (Polychromatic418967fa.accept_11_10_5_4_1_711
  21 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 81
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 81 (accept_3_4 19 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 38
  81 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 38 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 81 (accept_3_4 16 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 38 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 81 (Polychromatic418967fa.accept_15_14_8_6_1_2133
  14 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 38 81 (accept_3_4 13 38
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 38 81
  (Polychromatic418967fa.accept_28_12_10_25_1_3055 12 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 38 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 81 (accept_3_4 10 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 38 81 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 38 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 38
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 38 81 (accept_3_4 7 38 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 38
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 38 81
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 38 81 (accept_3_4 4 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 38 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 38 81 (Polychromatic418967fa.accept_13_2_12_3_1_415 2 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 81 (accept_3_4 1 38 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 81)))))))))))))))))))))))))))))))))))))) (allB_succ 37 81 (allA_succ_of_accept 36 37 81
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 81 (accept_3_5 35 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37
  81 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 37 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 81 (accept_3_5 32 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 37 81 (Polychromatic418967fa.accept_13_5_11_3_1_902 31 37 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 81 (Polychromatic418967fa.accept_14_2_9_11_1_3054
  30 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 81 (accept_3_5 29 37
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 81 (Polychromatic418967fa.accept_6_4_1_3_1_77
  28 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 81
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 81 (accept_3_5 26 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37
  81 (Polychromatic418967fa.accept_16_9_5_1_1_1259 25 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 81 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 81 (accept_3_5 23 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 81 (Polychromatic418967fa.accept_13_8_11_3_1_3053
  21 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 81 (accept_3_5 20 37
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 81 (Polychromatic418967fa.accept_7_5_2_4_1_126
  19 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 81
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 81 (accept_3_5 17 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37
  81 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 37 81 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 81 (accept_3_5 14 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 37 81 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 12
  37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 81 (accept_3_5 11 37 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 10
  37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 81
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 81 (accept_3_5 8 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 81
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 81 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 81 (accept_3_5 5 37 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 81 (Polychromatic418967fa.accept_12_3_1_9_1_202 3
  37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 81 (accept_3_5 2 37 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 81 (Polychromatic418967fa.accept_13_1_11_3_1_901 1
  37 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  81))))))))))))))))))))))))))))))))))))) (allB_succ 36 81 (allA_succ_of_accept 35 36 81
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 81 (Polychromatic418967fa.accept_19_15_17_5_1_3052 34 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 81 3 11 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 81 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 36 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 81
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 81 3 10 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 81 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 81 (Polychromatic418967fa.accept_13_2_10_3_1_1538 28 36 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 81 9 3 4 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 81
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 81 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 81 3 8 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 81 (Polychromatic418967fa.accept_17_6_2_13_1_3051 23 36 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 81
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 36 81 3 7 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 36 81 (Polychromatic418967fa.accept_13_7_10_3_1_1505 20 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 81 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 81 9 2 4 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 81
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 81 (Polychromatic418967fa.accept_21_16_15_18_1_3050 16 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 81 3 5 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 81 (Polychromatic418967fa.accept_16_14_4_1_1_3049 14 36 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 81
  (Polychromatic418967fa.accept_8_5_4_1_1_111 13 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 81 3 4 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 81 (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 81 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 36 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 81 9 1 4 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 81
  (Polychromatic418967fa.accept_16_8_4_1_1_2102 8 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 81 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 81 3 2 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 81 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 81
  (Polychromatic418967fa.accept_14_4_8_11_1_794 4 36 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 36 81 3 1 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 36 81 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 36 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 81 (Polychromatic418967fa.accept_17_1_2_13_1_2026 1 36 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 81))))))))))))))))))))))))))))))))))))
  (allB_succ 35 81 (allA_succ_of_accept 34 35 81 (accept_3_4 34 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 81 (Polychromatic418967fa.accept_13_7_9_3_1_1504 33 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 81 (accept_3_4 31 35 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 81
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 81 (accept_3_4 28 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35
  81 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 81 (accept_3_4 25 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 81 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 35 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 81 (Polychromatic418967fa.accept_31_23_4_19_1_3048
  23 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 81 (accept_3_4 22 35
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 81
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 81 (accept_3_4 19 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 81 (Polychromatic418967fa.accept_11_6_2_4_1_1703
  17 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 81 (accept_3_4 16 35
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 81
  (Polychromatic418967fa.accept_12_3_11_9_1_193 15 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 81 (accept_3_4 13 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 81 (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 35 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 81 (Polychromatic418967fa.accept_15_11_5_6_1_669
  11 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 81 (accept_3_4 10 35
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 81 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  9 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 81
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 81 (accept_3_4 7 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 81 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 81 (accept_3_4 4 35 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 81 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 35 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 81 (accept_3_4 1 35 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 81))))))))))))))))))))))))))))))))))) (allB_succ 34 81
  (allA_succ_of_accept 33 34 81 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 81 (accept_3_5 32 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 34 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 81 (Polychromatic418967fa.accept_7_2_6_4_1_29 30
  34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 81 (accept_3_5 29 34 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 81 (Polychromatic418967fa.accept_15_13_4_6_1_3046
  28 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 81 (accept_3_5 26 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 34
  81 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 34 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 81 (accept_3_5 23 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 34 81 (Polychromatic418967fa.accept_13_9_8_3_1_3045 22 34 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 81 (Polychromatic418967fa.accept_24_21_10_9_1_3044
  21 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 34 81 (accept_3_5 20 34
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 34 81 (Polychromatic418967fa.accept_4_3_2_1_1_50
  19 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 81
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 34 81 (accept_3_5 17 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34
  81 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 34 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 34 81 (accept_3_5 14 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 34 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 34 81 (Polychromatic418967fa.accept_7_5_6_4_1_117 12
  34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 81 (accept_3_5 11 34 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 10
  34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 81
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 81 (accept_3_5 8 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 81 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 81 (accept_3_5 5 34 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 81 (Polychromatic418967fa.accept_19_4_15_5_1_3043 4 34 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 81 (accept_3_5 2 34 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 81))))))))))))))))))))))))))))))))))
  (allB_succ 33 81 (allA_succ_of_accept 32 33 81 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 81
  (Polychromatic418967fa.accept_15_1_3_6_1_621 31 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 81 3 10 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 33 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 81 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 33 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 81 3 9 11 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 81
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 81 (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 33 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 81 3 8 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 33 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 81
  (Polychromatic418967fa.accept_7_1_5_4_1_134 22 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 81 3 7 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 81 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 33 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 81 (Polychromatic418967fa.accept_21_19_12_18_1_1798 19 33
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 81 3 6 11 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 81
  (Polychromatic418967fa.accept_13_4_7_3_1_92 17 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 81 3 5 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 81 (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 33 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 81
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 81 3 4 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 81 (Polychromatic418967fa.accept_13_11_7_3_1_894 11 33 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 81 (Polychromatic418967fa.accept_13_10_7_3_1_3041 10 33 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 81 3 3 11 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 81
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 81 (Polychromatic418967fa.accept_21_7_12_18_1_3040 7 33 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 81 3 2 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 81 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 33 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 81
  (Polychromatic418967fa.accept_13_4_7_3_1_92 4 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 81 3 1 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 33 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 33 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 81)))))))))))))))))))))))))))))))))
  (allB_succ 32 81 (allA_succ_of_accept 31 32 81 (accept_3_4 31 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 81 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 81 (accept_3_4 28 32 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 81 (Polychromatic418967fa.accept_11_5_10_4_1_1157
  27 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 81
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 81 (accept_3_4 25 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32
  81 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 81 (accept_3_4 22 32 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 81 (Polychromatic418967fa.accept_14_7_4_11_1_3038 21 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 81
  (Polychromatic418967fa.accept_21_20_11_18_1_3037 20 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 81 (accept_3_4 19 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32
  81 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 32 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 81 (accept_3_4 16 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 32 81 (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 32 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 81 (Polychromatic418967fa.accept_13_1_6_3_1_1547
  14 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 81 (accept_3_4 13 32
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 81
  (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 32 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 81 (accept_3_4 10 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 32 81 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 32 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 81 (Polychromatic418967fa.accept_14_8_4_11_1_3035 8
  32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 81 (accept_3_4 7 32 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 81 (Polychromatic418967fa.accept_10_6_2_1_1_494 6
  32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 81
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 81 (accept_3_4 4 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32 81
  (Polychromatic418967fa.accept_10_3_2_1_1_839 3 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 81 (Polychromatic418967fa.accept_17_2_15_13_1_3034 2 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 81 (accept_3_4 1 32 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 81)))))))))))))))))))))))))))))))) (allB_succ 31 81 (allA_succ_of_accept 30 31 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 81 (accept_3_5 29 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31
  81 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 31 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 31 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 81 (accept_3_5 26 31 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 31 81 (Polychromatic418967fa.accept_15_10_1_6_1_3033 25 31 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 81 (Polychromatic418967fa.accept_11_2_9_4_1_310 24
  31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 81 (accept_3_5 23 31 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 81
  (Polychromatic418967fa.accept_13_8_5_3_1_427 21 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 81 (accept_3_5 20 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31
  81 (Polychromatic418967fa.accept_13_6_5_3_1_426 19 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 81 (accept_3_5 17 31 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 81 (accept_3_5 14 31 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 81
  (Polychromatic418967fa.accept_20_12_11_1_1_3032 12 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 81 (accept_3_5 11 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31
  81 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 31 81 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 31 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 81 (accept_3_5 8 31 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 31 81 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 31 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 81 (accept_3_5 5 31 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 81
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 81 (accept_3_5 2 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 81
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 81))))))))))))))))))))))))))))))) (allB_succ 30 81 (allA_succ_of_accept 29 30 81
  (Polychromatic418967fa.accept_11_7_8_4_1_718 29 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 81 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 30 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 81 3 9 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 30 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 81
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 30 81 3 8 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 81 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 30 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 30 81 3 7 10 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 30 81
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 30 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 81 3 6 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 81 (Polychromatic418967fa.accept_18_17_12_9_1_3031 17 30 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 81
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 30 81 3 5 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 30 81 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 30 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 81 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 30 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 81 3 4 10 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 81 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 30 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 81 3 3 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 81 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 30 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 30 81 3 2 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 30 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 30 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 81 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 30 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 30 81 3 1 10 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 30 81
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 81 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 30 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 81)))))))))))))))))))))))))))))) (allB_succ 29 81 (allA_succ_of_accept 28
  29 81 (accept_3_4 28 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 81
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 81 (accept_3_4 25 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 81 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 81 (Polychromatic418967fa.accept_15_8_14_6_1_3003
  23 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 81 (accept_3_4 22 29
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 81
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 21 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 81 (accept_3_4 19 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 81 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 29 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 81 (Polychromatic418967fa.accept_7_3_1_4_1_121 17
  29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 81 (accept_3_4 16 29 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 81 (Polychromatic418967fa.accept_10_5_9_1_1_187 15
  29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 81
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 81 (accept_3_4 13 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29
  81 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 29 81 (Polychromatic418967fa.accept_17_11_12_13_1_3030 11 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 81 (accept_3_4 10 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 29 81 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 29 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 81 (accept_3_4 7 29 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 81 (Polychromatic418967fa.accept_30_6_29_21_1_3029
  6 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 81
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 81 (accept_3_4 4 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 81
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 81 (accept_3_4 1 29 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 81))))))))))))))))))))))))))))) (allB_succ 28 81 (allA_succ_of_accept 27 28 81
  (Polychromatic418967fa.accept_13_1_2_3_1_911 27 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 81 (accept_3_5 26 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 28
  81 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 28 81 (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 28 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 81 (accept_3_5 23 28 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 28 81 (Polychromatic418967fa.accept_13_9_2_3_1_3027 22 28 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 81 (Polychromatic418967fa.accept_8_5_4_1_1_111 21
  28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 81 (accept_3_5 20 28 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 81
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 81 (accept_3_5 17 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28
  81 (Polychromatic418967fa.accept_23_16_5_12_1_3026 16 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 81 (Polychromatic418967fa.accept_17_15_11_13_1_2039 15 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 81 (accept_3_5 14 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 28 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 81
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 81 (accept_3_5 11 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28
  81 (Polychromatic418967fa.accept_13_10_2_3_1_3025 10 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 81 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 28 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 81 (accept_3_5 8 28 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 28 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 81 (Polychromatic418967fa.accept_12_6_4_9_1_544 6
  28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 81 (accept_3_5 5 28 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 81 (Polychromatic418967fa.accept_15_4_13_6_1_642 4
  28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 81
  (Polychromatic418967fa.accept_10_3_8_1_1_182 3 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 81 (accept_3_5 2 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 81
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 81)))))))))))))))))))))))))))) (allB_succ 27 81 (allA_succ_of_accept 26 27 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 81 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 27 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 81 3 8 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 81 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 27 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 81 3 7 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 81 (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 27 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 81 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 27 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 81 9 2 3 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 81
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 81 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 27 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 81 3 5 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 81
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 81 3 4 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 81 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 27 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 81 9 1 3 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 81
  (Polychromatic418967fa.accept_20_8_7_1_1_3024 8 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 81 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 27 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 81 3 2 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 81 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 27 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 81
  (Polychromatic418967fa.accept_10_4_7_1_1_471 4 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 81 3 1 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 81 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 81))))))))))))))))))))))))))) (allB_succ 26 81
  (allA_succ_of_accept 25 26 81 (accept_3_4 25 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26
  81 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 81 (accept_3_4 22 26 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 81 (Polychromatic418967fa.accept_17_4_9_13_1_2020 21 26 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 81 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 81 (accept_3_4 19 26 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 81 (Polychromatic418967fa.accept_12_6_2_9_1_537 18
  26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 81
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 81 (accept_3_4 16 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 26
  81 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 26 81 (Polychromatic418967fa.accept_20_14_6_1_1_3023 14 26 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 81 (accept_3_4 13 26 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 26 81 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 26 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 81 (accept_3_4 10 26 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 26
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 81
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 81 (accept_3_4 7 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 81
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 81 (accept_3_4 4 26 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 26
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 81 (accept_3_4 1 26 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 81)))))))))))))))))))))))))) (allB_succ 25 81
  (allA_succ_of_accept 24 25 81 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 25 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 81 (accept_3_5 23 25 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 81 (Polychromatic418967fa.accept_16_5_9_1_1_2070
  21 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 81 (accept_3_5 20 25
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 81
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 81 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 25 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 81 (accept_3_5 17 25 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 81 (Polychromatic418967fa.accept_12_3_1_9_1_202 15
  25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 81 (accept_3_5 14 25 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 81 (Polychromatic418967fa.accept_16_13_9_1_1_3022
  13 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 81
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 81 (accept_3_5 11 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25
  81 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 25 81 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 25 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 81 (accept_3_5 8 25 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 25 81 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 25 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 81 (Polychromatic418967fa.accept_10_6_5_1_1_482 6
  25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 81 (accept_3_5 5 25 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 81
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 81 (accept_3_5 2 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 81
  (Polychromatic418967fa.accept_15_1_10_6_1_631 1 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 81))))))))))))))))))))))))) (allB_succ 24 81 (allA_succ_of_accept 23 24 81
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 24 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 81 3 7 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 24 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 81
  (Polychromatic418967fa.accept_15_4_9_6_1_627 19 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 81 3 6 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 81 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 24 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 81 (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 24 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 24 81 3 5 8 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 24 81
  (Polychromatic418967fa.accept_13_1_11_3_1_901 14 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 81 3 4 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 81 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 24 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 81
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 24 81 3 3 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 24 81 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 24 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 81 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 24 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 81 3 2 8 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 81
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 81 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 24 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 81 3 1 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 81 (Polychromatic418967fa.accept_13_2_11_3_1_873 2 24 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 81
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 81)))))))))))))))))))))))) (allB_succ 23 81 (allA_succ_of_accept 22 23 81 (accept_3_4 22 23 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 81 (Polychromatic418967fa.accept_19_2_4_5_1_3021 21 23 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 81
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 81 (accept_3_4 19 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 23
  81 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 23 81 (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 23 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 81 (accept_3_4 16 23 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 23 81 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 23 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 81 (accept_3_4 13 23 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 12
  23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 81
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 81 (accept_3_4 10 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23
  81 (Polychromatic418967fa.accept_19_9_4_5_1_3019 9 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 81 (accept_3_4 7 23 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 81 (accept_3_4 4 23 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 81 (Polychromatic418967fa.accept_12_3_11_9_1_193 3
  23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 81 (accept_3_4 1 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  81))))))))))))))))))))))) (allB_succ 22 81 (allA_succ_of_accept 21 22 81 (Polychromatic418967fa.accept_13_8_9_3_1_2213
  21 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 81 (accept_3_5 20 22
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22 81 (Polychromatic418967fa.accept_4_3_2_1_1_50
  19 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 22 81
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 22 81 (accept_3_5 17 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22
  81 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 22 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 81 (accept_3_5 14 22 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 22 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 81 (Polychromatic418967fa.accept_7_5_1_4_1_122 12
  22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 81 (accept_3_5 11 22 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 81 (Polychromatic418967fa.accept_7_3_1_4_1_121 10
  22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 81
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 81 (accept_3_5 8 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 81 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 22 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 81 (accept_3_5 5 22 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 81 (Polychromatic418967fa.accept_14_4_8_11_1_794 4 22 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 81 (accept_3_5 2 22 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 81)))))))))))))))))))))) (allB_succ 21 81
  (allA_succ_of_accept 20 21 81 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 21 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 81 (Polychromatic418967fa.accept_18_1_3_9_1_328 19 21 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 81 3 6 7 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 81
  (Polychromatic418967fa.accept_14_3_7_11_1_765 17 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 81 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 21 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 81 3 5 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 81 (Polychromatic418967fa.accept_17_14_4_13_1_3018 14 21 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 81
  (Polychromatic418967fa.accept_16_13_5_1_1_3017 13 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 81 3 4 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 81 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 21 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 81 (Polychromatic418967fa.accept_14_10_7_11_1_3015 10 21 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 81 3 3 7 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 81
  (Polychromatic418967fa.accept_17_8_4_13_1_3014 8 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 81 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 21 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 81 3 2 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 81 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 21 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 81
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 81 3 1 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 81 (Polychromatic418967fa.accept_18_2_3_9_1_1996 2 21 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 81 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 21 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 81))))))))))))))))))))) (allB_succ 20 81
  (allA_succ_of_accept 19 20 81 (accept_3_4 19 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20
  81 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 81 (accept_3_4 16 20 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 81 (Polychromatic418967fa.accept_19_15_1_5_1_3013 15 20 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 81 (Polychromatic418967fa.accept_13_1_7_3_1_1503
  14 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 81 (accept_3_4 13 20
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 81 (Polychromatic418967fa.accept_7_5_6_4_1_117
  12 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 81
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 20 81 (accept_3_4 10 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 20
  81 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 20 81 (Polychromatic418967fa.accept_13_8_7_3_1_430 8 20 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 81 (accept_3_4 7 20 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 20 81 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 20 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 81 (accept_3_4 4 20 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 20
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 81
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 81 (accept_3_4 1 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  81)))))))))))))))))))) (allB_succ 19 81 (allA_succ_of_accept 18 19 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 81 (accept_3_5 17 19 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 81
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 81 (accept_3_5 14 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19
  81 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 19 81 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 19 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 81 (accept_3_5 11 19 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 19 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 19
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 81 (accept_3_5 8 19 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 81 (Polychromatic418967fa.accept_11_7_8_4_1_718 7
  19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 81 (accept_3_5 5 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 81
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 81 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 19 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 81 (accept_3_5 2 19 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 81))))))))))))))))))) (allB_succ 18 81 (allA_succ_of_accept 17
  18 81 (Polychromatic418967fa.accept_19_17_18_5_1_3012 17 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 81 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 18 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 81 3 5 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 81 (Polychromatic418967fa.accept_11_3_7_4_1_1133 14
  18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 81
  (Polychromatic418967fa.accept_10_3_8_1_1_182 13 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 81 3 4 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 81 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 18 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 81 9 1 2 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 81
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 81 3 2 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 81 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 18 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 81
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 81 3 1 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 81 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 18 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 81 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 18 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 81)))))))))))))))))) (allB_succ 17 81
  (allA_succ_of_accept 16 17 81 (accept_3_4 16 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17
  81 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 81 (accept_3_4 13 17 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 81 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 17 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 81 (Polychromatic418967fa.accept_15_11_2_6_1_3010
  11 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 81 (accept_3_4 10 17
  81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 81
  (Polychromatic418967fa.accept_21_9_17_18_1_3009 9 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 81 (accept_3_4 7 17 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 81 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 17 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 81 (Polychromatic418967fa.accept_23_5_17_12_1_3008
  5 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 81 (accept_3_4 4 17 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 81 (Polychromatic418967fa.accept_12_3_5_9_1_176 3
  17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 81
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 81 (accept_3_4 1 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  81))))))))))))))))) (allB_succ 16 81 (allA_succ_of_accept 15 16 81 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 16
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 81 (accept_3_5 14 16 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 81
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 81 (accept_3_5 11 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16
  81 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 16 81 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 16 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 81 (accept_3_5 8 16 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 16 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 81 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 16
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 81 (accept_3_5 5 16 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 81 (Polychromatic418967fa.accept_22_4_16_15_1_3007
  4 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 81
  (Polychromatic418967fa.accept_15_3_1_6_1_206 3 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 81 (accept_3_5 2 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 81
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 81)))))))))))))))) (allB_succ 15 81 (allA_succ_of_accept 14 15 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 81 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 15 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 81 3 4 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 81 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 15 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 81 3 3 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 81 (Polychromatic418967fa.accept_16_8_15_1_1_3006 8 15 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 81 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 15 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 81 3 2 5 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 81
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 81 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 15 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 81 3 1 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 81
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 81))))))))))))))) (allB_succ 14 81 (allA_succ_of_accept 13 14 81 (accept_3_4 13 14 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 81 (Polychromatic418967fa.accept_21_12_14_18_1_3005 12 14 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 81
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 81 (accept_3_4 10 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14
  81 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 81 (Polychromatic418967fa.accept_15_8_14_6_1_3003 8 14 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 81 (accept_3_4 7 14 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 14 81 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 14 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 81 (accept_3_4 4 14 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 81
  (Polychromatic418967fa.accept_13_2_1_3_1_419 2 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 81 (accept_3_4 1 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  81)))))))))))))) (allB_succ 13 81 (allA_succ_of_accept 12 13 81 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 81 (accept_3_5 11 13 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 10
  13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 81
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 13 81 (accept_3_5 8 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 81
  (Polychromatic418967fa.accept_15_7_13_6_1_696 7 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 13 81 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 13 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 81 (accept_3_5 5 13 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 13 81 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 81 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 13
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 81 (accept_3_5 2 13 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 81 (Polychromatic418967fa.accept_23_1_13_12_1_3002
  1 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 81))))))))))))) (allB_succ 12 81
  (allA_succ_of_accept 11 12 81 (Polychromatic418967fa.accept_16_11_12_1_1_3001 11 12 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 81 (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 12 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 81 3 3 4 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 81
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 81 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 12 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 81 3 2 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 81 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 81
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 12 81 3 1 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 12 81 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 12 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 81 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 81)))))))))))) (allB_succ 11 81
  (allA_succ_of_accept 10 11 81 (accept_3_4 10 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11
  81 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 81 (accept_3_4 7 11 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 81 (Polychromatic418967fa.accept_13_5_11_3_1_902 5
  11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 81 (accept_3_4 4 11 81
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 81 (Polychromatic418967fa.accept_12_3_11_9_1_193 3
  11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 81 (accept_3_4 1 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 81)))))))))))
  (allB_succ 10 81 (allA_succ_of_accept 9 10 81 (Polychromatic418967fa.accept_16_9_10_1_1_2998 9 10 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 81 (accept_3_5 8 10 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 81
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 81 (accept_3_5 5 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10 81
  (Polychromatic418967fa.accept_15_4_10_6_1_2997 4 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 81 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 81 (accept_3_5 2 10 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 81 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 81)))))))))) (allB_succ 9 81 (allA_succ_of_accept 8 9 81
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 9 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 81 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 9 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 81 3 2 3 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 81 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 81
  (Polychromatic418967fa.accept_15_4_9_6_1_627 4 9 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 81 3 1 3 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 81 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 9 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 81 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 9 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 81))))))))) (allB_succ 8 81
  (allA_succ_of_accept 7 8 81 (accept_3_4 7 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 81
  (Polychromatic418967fa.accept_12_6_8_9_1_553 6 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 81 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 81 (accept_3_4 4 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 8 81 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 81 (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 8 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 81 (accept_3_4 1 8 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 8 81)))))))) (allB_succ 7 81 (allA_succ_of_accept 6 7 81
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 81 (accept_3_5 5 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 81
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 81 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 7 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 81 (accept_3_5 2 7 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 81 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 7 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 81))))))) (allB_succ 6 81 (allA_succ_of_accept 5 6 81
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 6 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 81 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 6 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 81 3 1 2 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 81 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 6 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 81
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 6 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 81)))))) (allB_succ 5 81 (allA_succ_of_accept 4 5 81 (accept_3_4 4 5 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 81 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 5 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 81 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 81 (accept_3_4 1 5 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 81))))) (allB_succ 4 81 (allA_succ_of_accept 3 4 81
  (Polychromatic418967fa.accept_16_3_4_1_1_2996 3 4 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 81 (accept_3_5 2 4 81 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 81
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 81)))) (allB_succ 3 81 (allA_succ_of_accept 2 3 81 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 81
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 3 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 81))) (allB_succ 2 81 (allA_succ_of_accept 1 2 81 (accept_3_4 1 2 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 81)) (allB_two
  81)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


