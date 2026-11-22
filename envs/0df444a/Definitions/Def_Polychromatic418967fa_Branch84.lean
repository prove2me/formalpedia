-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch84
-- name    : Polychromatic418967fa_Branch84
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:07.015405+00:00
-- url     : https://prove2.me/theorems/5bae86c7-a63e-48fe-be6d-a07feadb80d1
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

def Polychromatic418967fa.branch_84 : allB 84 84 :=
  allB_succ' 2 83 84 (Eq.refl Bool.true) (allA_succ_of_accept 1 83 84 (accept_3_4 1 83 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 84)) (allB_succ' 3 82 84 (Eq.refl Bool.true) (allA_succ_of_gcd 2 82 84 2 1 41 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 84
  (Polychromatic418967fa.accept_15_1_7_9_1_20 1 82 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 84))) (allB_succ' 4 81 84 (Eq.refl Bool.true) (allA_succ_of_gcd 3 81 84 3 1 27 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 84
  (Polychromatic418967fa.accept_19_2_5_8_1_2081 2 81 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 84 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 81 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81 84)))) (allB_succ' 5 80 84 (Eq.refl Bool.true) (allA_succ_of_gcd 4 80 84
  4 1 20 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 84
  (Polychromatic418967fa.accept_15_3_5_9_1_764 3 80 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 84 2 1 40 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 84 (accept_3_4 1 80 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80 84)))))
  (allB_succ' 6 79 84 (Eq.refl Bool.true) (allA_succ_of_accept 5 79 84 (accept_3_5 5 79 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 79 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 79 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 79
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 84 (accept_3_5 2 79 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 79
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 84)))))) (allB_succ' 7 78 84 (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 78 84 6 1 13 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 78 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 84 2 2 39 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 78 84 3 1 26 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 78 84 2 1 39 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 78
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 84))))))) (allB_succ' 8 77 84 (Eq.refl
  Bool.true) (allA_succ_of_gcd 7 77 84 7 1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 77 84 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 77 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 84 (Polychromatic418967fa.accept_13_5_12_6_1_508 5
  77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 84 (accept_3_4 4 77 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 84 (Polychromatic418967fa.accept_10_3_7_4_1_584 3
  77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 84
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 84 (accept_3_4 1 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 84))))))))
  (allB_succ' 9 76 84 (Eq.refl Bool.true) (allA_succ_of_gcd 8 76 84 4 2 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 84 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 76
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 84 2 3 38 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 84 (accept_3_5 5 76
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 84 4 1 19 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76 84
  (Polychromatic418967fa.accept_11_3_10_7_1_129 3 76 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 84 2 1 38 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 76 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76 84))))))))) (allB_succ' 10 75 84 (Eq.refl Bool.true) (allA_succ_of_gcd 9
  75 84 3 3 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8
  75 84 (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 75 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 75 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 75 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 84 3 2 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 84 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 75
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 84
  (Polychromatic418967fa.accept_13_4_10_6_1_989 4 75 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 84 3 1 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 84 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 75 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 84 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 75 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 84)))))))))) (allB_succ' 11 74 84 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 74 84 2 5 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 84 (Polychromatic418967fa.accept_17_9_6_16_1_3280 9 74 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 84 2 4 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 84 (accept_3_4 7 74 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 84 2 3 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 74 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 84 2 2 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 84 (Polychromatic418967fa.accept_13_3_9_6_1_502 3 74
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 84 2 1 37 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 84 (accept_3_4 1 74
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 84))))))))))) (allB_succ' 12 73 84 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 73 84 (accept_3_5 11 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 73
  84 (Polychromatic418967fa.accept_19_10_16_8_1_3289 10 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 84 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 73 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 84 (accept_3_5 8 73 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 73 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 73 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 84 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 73
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 84 (accept_3_5 5 73 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73 84 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 73
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 84
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 3 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 73 84 (accept_3_5 2 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 84
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 73 84)))))))))))) (allB_succ' 13 72 84 (Eq.refl Bool.true) (allA_succ_of_gcd 12 72 84 12 1 6 7 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 84
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 11 72 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 84 2 5 36 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 72 84 3 3 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 72 84 4 2 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 84 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 72 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 84 6 1 12 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 84 (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 72 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 84 4 1 18 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 84 3 1 24 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 84 2 1 36 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 84
  (Polychromatic418967fa.accept_11_1_6_7_1_116 1 72 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 84))))))))))))) (allB_succ' 14 71 84 (Eq.refl Bool.true) (allA_succ_of_accept 13 71 84 (accept_3_4 13 71
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 84
  (Polychromatic418967fa.accept_16_12_7_4_1_687 12 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 71 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 71 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 84 (accept_3_4 10 71 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 71 84 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 71 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 84 (Polychromatic418967fa.accept_16_8_7_4_1_2217 8
  71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 84 (accept_3_4 7 71 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 84 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 71
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 84
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 84 (accept_3_4 4 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 84
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 71 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 84 (accept_3_4 1 71 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 84)))))))))))))) (allB_succ' 15 70 84 (Eq.refl Bool.true) (allA_succ_of_gcd 14 70 84 14 1 5 6
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 84
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 70 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 84 2 6 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 84 (accept_3_5 11 70 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 84
  2 5 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 84
  (Polychromatic418967fa.accept_18_9_16_12_1_1143 9 70 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 84 2 4 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 70 84 7 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 70 84 2 3 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 70 84 (accept_3_5 5 70 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 84 2
  2 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 84
  (Polychromatic418967fa.accept_11_3_4_7_1_114 3 70 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 70 84 2 1 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 70 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 70 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 70 84))))))))))))))) (allB_succ' 16 69 84 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 69 84 3 5 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 69 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 69 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 84 3 4 23 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 84
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 69 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 84 3 3 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 84 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 69 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 84
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 84 3 2 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 69 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 69 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 84 3 1 23 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 84
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 69 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 84)))))))))))))))) (allB_succ' 17 68 84 (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 68 84 4 4 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 68 84 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 68 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 84 2 7 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 84 (accept_3_4 13 68 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 68 84 4 3 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 68 84 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 68 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 84 2 5 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 84 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 68
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 84 4 2 17 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 84 (accept_3_4 7 68
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 84 2 3 34 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68 84
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 84 4 1 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 84 (Polychromatic418967fa.accept_15_3_8_9_1_795 3 68 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 84 2 1 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 84 (accept_3_4 1 68 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 84))))))))))))))))) (allB_succ' 18 67 84 (Eq.refl Bool.true) (allA_succ_of_accept 17 67 84
  (accept_3_5 17 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 84
  (Polychromatic418967fa.accept_9_7_4_3_1_204 16 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 67 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 67 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 84 (accept_3_5 14 67 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 67 84 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 67 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 84 (Polychromatic418967fa.accept_10_2_7_4_1_967 12
  67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 84 (accept_3_5 11 67 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 10
  67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 84
  (Polychromatic418967fa.accept_13_9_2_6_1_514 9 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 84 (accept_3_5 8 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 84
  (Polychromatic418967fa.accept_8_7_3_4_1_404 7 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 67 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 84 (accept_3_5 5 67 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 84 (Polychromatic418967fa.accept_13_4_2_6_1_1043 4 67 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 84 (Polychromatic418967fa.accept_10_3_7_4_1_584 3
  67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 84 (accept_3_5 2 67 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 67
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 84)))))))))))))))))) (allB_succ' 19 66 84
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 66 84 6 3 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 66 84 (Polychromatic418967fa.accept_19_17_9_8_1_3269 17 66 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 84 2 8 33 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 84 3 5 22 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 84 2 7 33 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 84
  (Polychromatic418967fa.accept_24_13_18_12_1_3288 13 66 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 84 6 2 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 84 (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 66 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 84 2 5 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 66 84 3 3 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 66 84 2 4 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 84 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 66 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 84 6 1 11 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 84
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 66 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 84 2 2 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 66 84 3 1 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 66 84 2 1 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 84 (Polychromatic418967fa.accept_15_1_6_9_1_254 1 66 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 84))))))))))))))))))) (allB_succ' 20 65 84 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 65 84 (accept_3_4 19 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65
  84 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 84 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 84 (accept_3_4 16 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 65 84 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 65 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 14
  65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 84 (accept_3_4 13 65 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 84 (Polychromatic418967fa.accept_15_12_5_9_1_3234
  12 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 84
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 84 (accept_3_4 10 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65
  84 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 84 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 84 (accept_3_4 7 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 84 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 65 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 65
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 84 (accept_3_4 4 65 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 84 (Polychromatic418967fa.accept_11_3_10_7_1_129 3
  65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 84
  (Polychromatic418967fa.accept_17_2_14_16_1_2187 2 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 84 (accept_3_4 1 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  84)))))))))))))))))))) (allB_succ' 21 64 84 (Eq.refl Bool.true) (allA_succ_of_gcd 20 64 84 4 5 16 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 84
  (Polychromatic418967fa.accept_23_19_18_15_1_3286 19 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 84 2 9 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 84 (accept_3_5 17 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 84
  4 4 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 64
  84 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 64 84 2 7 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 64 84 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 64 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 84 4 3 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 84 (accept_3_5 11 64 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 64 84 2 5 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 64 84 (Polychromatic418967fa.accept_17_9_13_16_1_3266 9 64 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 84 4 2 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 64
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 84 2 3 32 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 84 (accept_3_5 5 64
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 84 4 1 16 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64 84
  (Polychromatic418967fa.accept_17_3_13_16_1_2183 3 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 84 2 1 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 84 (Polychromatic418967fa.accept_19_1_7_8_1_3262 1 64 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 84))))))))))))))))))))) (allB_succ' 22 63 84 (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 63 84 21 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 84 (Polychromatic418967fa.accept_15_5_3_9_1_283 20 63 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 63 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 84 3 6 21 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 84
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 84 (Polychromatic418967fa.accept_18_16_9_12_1_1182 16 63 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 84 3 5 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 63 84 7 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 84 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 63 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 84 3 4 21 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 84
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 84 (Polychromatic418967fa.accept_15_10_3_9_1_3285 10 63 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 84 3 3 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 84 (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 63 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 84 7 1 9 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 63 84 3 2 21 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 84
  (Polychromatic418967fa.accept_13_5_11_6_1_505 5 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 84 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 63 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 84 3 1 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 84 (Polychromatic418967fa.accept_19_2_6_8_1_3284 2 63 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 84
  (Polychromatic418967fa.accept_17_1_12_16_1_2211 1 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 84)))))))))))))))))))))) (allB_succ' 23 62 84 (Eq.refl Bool.true) (allA_succ_of_gcd 22 62 84 2 11 31 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 84
  (Polychromatic418967fa.accept_18_3_8_12_1_3283 21 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 84 2 10 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 62 84 (accept_3_4 19 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 84
  2 9 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 62
  84 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 62 84 2 8 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 62 84 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 62 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 84 2 7 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 84 (accept_3_4 13 62 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 62 84 2 6 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 62 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 62 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 62 84 2 5 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 62 84 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9
  62 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 84 2 4 31 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 84 (accept_3_4 7 62
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 84 2 3 31 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 62 84
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 62 84 2 2 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 62 84 (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 62 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 84 2 1 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 84 (accept_3_4 1 62 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 84))))))))))))))))))))))) (allB_succ' 24 61 84 (Eq.refl Bool.true) (allA_succ_of_accept 23 61
  84 (accept_3_5 23 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 84
  (Polychromatic418967fa.accept_9_4_7_3_1_43 22 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 61 84 (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 61 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 84 (accept_3_5 20 61 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 61 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 61 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 84 (Polychromatic418967fa.accept_19_18_4_8_1_3282
  18 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 84 (accept_3_5 17 61
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 84 (Polychromatic418967fa.accept_13_3_9_6_1_502
  16 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 84
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 84 (accept_3_5 14 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61
  84 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 61 84 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 61 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 84 (accept_3_5 11 61 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 61 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 61 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 61
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 84 (accept_3_5 8 61 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 84 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7
  61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 84
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 84 (accept_3_5 5 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 84
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 84 (Polychromatic418967fa.accept_13_3_9_6_1_502 3 61 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 84 (accept_3_5 2 61 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 61 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 84)))))))))))))))))))))))) (allB_succ' 25 60 84 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 60 84 12 2 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 60 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 60 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 84 2 11 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 84 3 7 20 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 84 4 5 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 19
  60 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 84 6 3 10 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 84
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 60 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 60 84 4 4 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 60 84 3 5 20 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 60 84 2 7 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 60 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 84 12 1 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 84 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 60 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 84 2 5 30 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 84 3 3 20 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 84 4 2 15 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 84
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 60 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 84 6 1 10 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 60 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 84 4 1 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 84 3 1 20 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 84 2 1 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 60 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 84))))))))))))))))))))))))) (allB_succ' 26
  59 84 (Eq.refl Bool.true) (allA_succ_of_accept 25 59 84 (accept_3_4 25 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 59 84 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 59 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 84 (accept_3_4 22 59 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 84 (Polychromatic418967fa.accept_15_6_14_9_1_1471
  21 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 84
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 84 (accept_3_4 19 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59
  84 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 59 84 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 84 (accept_3_4 16 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 59 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 59 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 84 (Polychromatic418967fa.accept_11_3_4_7_1_114 14
  59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 84 (accept_3_4 13 59 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 84 (Polychromatic418967fa.accept_13_12_7_6_1_1015
  12 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 84
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 84 (accept_3_4 10 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59
  84 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 84 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 84 (accept_3_4 7 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 84 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 59 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 84 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5
  59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 84 (accept_3_4 4 59 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 84 (Polychromatic418967fa.accept_10_3_9_4_1_960 3
  59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 84
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 84 (accept_3_4 1 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  84)))))))))))))))))))))))))) (allB_succ' 27 58 84 (Eq.refl Bool.true) (allA_succ_of_gcd 26 58 84 2 13 29 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 84
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 84 2 12 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 58 84 (accept_3_5 23 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 84
  2 11 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58
  84 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 58 84 2 10 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 58 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 58 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 84 2 9 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 84 (accept_3_5 17 58 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58 84 2 8 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 58 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 58 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 84 2 7 29 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 84
  (Polychromatic418967fa.accept_19_13_1_8_1_3281 13 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 58 84 2 6 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 58 84 (accept_3_5 11 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 84
  2 5 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 84
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 84 2 4 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 84 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 58 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 84 2 3 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 84 (accept_3_5 5 58 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 84 2 2 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 84 (Polychromatic418967fa.accept_15_3_13_9_1_3196 3 58 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 84 2 1 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 58
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 84))))))))))))))))))))))))))) (allB_succ'
  28 57 84 (Eq.refl Bool.true) (allA_succ_of_gcd 27 57 84 3 9 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 84 (Polychromatic418967fa.accept_17_9_6_16_1_3280 26 57 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 84
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 84 3 8 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 84 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 84 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 57 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 84 3 7 19 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 84
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 84 (Polychromatic418967fa.accept_15_4_12_9_1_773 19 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 84 3 6 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 84 (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 57 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 84
  (Polychromatic418967fa.accept_13_3_5_6_1_3192 16 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 84 3 5 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 84 (Polychromatic418967fa.accept_13_1_5_6_1_1048 14 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 57 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 84 3 4 19 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 84
  (Polychromatic418967fa.accept_10_1_7_4_1_968 11 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 84 (Polychromatic418967fa.accept_13_10_5_6_1_1671 10 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 84 3 3 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 84 (Polychromatic418967fa.accept_16_8_9_4_1_630 8 57 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 84
  (Polychromatic418967fa.accept_17_7_6_16_1_2195 7 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 84 3 2 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 84 (Polychromatic418967fa.accept_13_4_5_6_1_3201 4 57 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 84 3 1 19 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 84
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 84 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 84)))))))))))))))))))))))))))) (allB_succ' 29 56 84 (Eq.refl Bool.true)
  (allA_succ_of_gcd 28 56 84 28 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 84 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 56 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 84 2 13 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 84 (accept_3_4 25 56 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 56 84 4 6 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 56 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 56 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 84 2 11 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 56 84 7 3 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 56 84 4 5 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 84 (accept_3_4 19 56 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 84 2 9 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 56 84 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 56 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 84 4 4 14 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 84
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 84 14 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 84 (accept_3_4 13 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 84
  4 3 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56
  84 (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 84 2 5 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 84 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 56 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 84 4 2 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 56 84 7 1 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 56 84 2 3 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 56
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 84 4 1 14 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 84
  (Polychromatic418967fa.accept_16_3_8_4_1_3279 3 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 84 2 1 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 84 (accept_3_4 1 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  84))))))))))))))))))))))))))))) (allB_succ' 30 55 84 (Eq.refl Bool.true) (allA_succ_of_accept 29 55 84 (accept_3_5 29
  55 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 84
  (Polychromatic418967fa.accept_16_12_7_4_1_687 28 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 55 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 84 (accept_3_5 26 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 55 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 55 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 84 (Polychromatic418967fa.accept_9_6_1_3_1_191 24
  55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 84 (accept_3_5 23 55 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 84 (Polychromatic418967fa.accept_9_4_1_3_1_190 22
  55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 84
  (Polychromatic418967fa.accept_10_1_5_4_1_276 21 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 84 (accept_3_5 20 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55
  84 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 84 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 84 (accept_3_5 17 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 55 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 84 (Polychromatic418967fa.accept_9_6_1_3_1_191 15
  55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 84 (accept_3_5 14 55 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 84 (Polychromatic418967fa.accept_9_4_1_3_1_190 13
  55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 84
  (Polychromatic418967fa.accept_15_12_10_9_1_798 12 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 84 (accept_3_5 11 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55
  84 (Polychromatic418967fa.accept_13_10_3_6_1_1003 10 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 84 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 55 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 84 (accept_3_5 8 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 55 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 55 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 84 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 55
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 84 (accept_3_5 5 55 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 84 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 55
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 84
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 84 (accept_3_5 2 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 84
  (Polychromatic418967fa.accept_10_1_5_4_1_276 1 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 84)))))))))))))))))))))))))))))) (allB_succ' 31 54 84 (Eq.refl Bool.true) (allA_succ_of_gcd 30 54 84 6 5
  9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 84
  (Polychromatic418967fa.accept_16_13_6_4_1_3277 29 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 84 2 14 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 54 84 3 9 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 54 84 2 13 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 84 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 54 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 84 6 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 84 (Polychromatic418967fa.accept_13_10_2_6_1_1044 23 54 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 84 2 11 27 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 84 3 7 18 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 54 84 2 10 27 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 84
  (Polychromatic418967fa.accept_16_3_6_4_1_679 19 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 84 6 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 84 (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 54 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 84 2 8 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 84 3 5 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 84 2 7 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 84 (Polychromatic418967fa.accept_16_13_6_4_1_3277 13 54 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 84 6 2 9 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 84
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 11 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 84 2 5 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 54 84 3 3 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 54 84 2 4 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 84 (Polychromatic418967fa.accept_17_7_3_16_1_2208 7 54 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 84 6 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 84 (Polychromatic418967fa.accept_16_5_6_4_1_3211 5 54 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 84 2 2 27 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 84 3 1 18 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 84 2 1 27 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 84
  (Polychromatic418967fa.accept_13_1_2_6_1_515 1 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 84))))))))))))))))))))))))))))))) (allB_succ' 32 53 84 (Eq.refl Bool.true) (allA_succ_of_accept 31 53 84
  (accept_3_4 31 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 84
  (Polychromatic418967fa.accept_22_8_9_18_1_3276 30 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 53 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 84 (accept_3_4 28 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 53 84 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 84 (Polychromatic418967fa.accept_19_7_15_8_1_1089
  26 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 84 (accept_3_4 25 53
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 84 (Polychromatic418967fa.accept_9_6_8_3_1_183
  24 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 84
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 84 (accept_3_4 22 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53
  84 (Polychromatic418967fa.accept_13_8_1_6_1_997 21 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 53 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 84 (accept_3_4 19 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 53 84 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 17
  53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 84 (accept_3_4 16 53 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 84 (Polychromatic418967fa.accept_9_6_8_3_1_183 15
  53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 84
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 84 (accept_3_4 13 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53
  84 (Polychromatic418967fa.accept_16_12_5_4_1_3275 12 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 84 (accept_3_4 10 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 53 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 84
  (Polychromatic418967fa.accept_13_8_1_6_1_997 8 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 84 (accept_3_4 7 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 84
  (Polychromatic418967fa.accept_9_6_8_3_1_183 6 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 84 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 84 (accept_3_4 4 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 84 (Polychromatic418967fa.accept_13_3_1_6_1_509 3 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 53
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 84 (accept_3_4 1 53 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 84)))))))))))))))))))))))))))))))) (allB_succ' 33 52 84 (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 52 84 4 8 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 52 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 52 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 84 2 15 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 84 (accept_3_5 29 52 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 84 4 7 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 52 84 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 84 2 13 26 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 84
  (Polychromatic418967fa.accept_19_6_14_8_1_3274 25 52 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 84 4 6 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 84 (accept_3_5 23 52 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 84
  2 11 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52
  84 (Polychromatic418967fa.accept_19_2_14_8_1_3273 21 52 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 84 4 5 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 52 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 52 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 84 2 9 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 84 (accept_3_5 17 52 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 84 4 4 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 52 84 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 84 2 7 26 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 84
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 52 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 84 4 3 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 84 (accept_3_5 11 52 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 84
  2 5 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 84
  (Polychromatic418967fa.accept_18_9_16_12_1_1143 9 52 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 84 4 2 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 84 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 52 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 84 2 3 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 84 (accept_3_5 5 52 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 84 4 1 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 84 (Polychromatic418967fa.accept_19_3_14_8_1_3272 3 52 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 84 2 1 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 52
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 84)))))))))))))))))))))))))))))))))
  (allB_succ' 34 51 84 (Eq.refl Bool.true) (allA_succ_of_gcd 33 51 84 3 11 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 51
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 84
  (Polychromatic418967fa.accept_8_7_3_4_1_404 31 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 84 3 10 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 84 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 51 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 84 3 9 17 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 84
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 84 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 84 3 8 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 51 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 84
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 84 3 7 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 84 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 51 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 84 3 6 17 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 84
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 84 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 84 3 5 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 51 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 84
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 84 3 4 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 84 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 51 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 84 3 3 17 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 84
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 84 3 2 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 51 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 84
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 84 3 1 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 84 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 51 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 84))))))))))))))))))))))))))))))))))
  (allB_succ' 35 50 84 (Eq.refl Bool.true) (allA_succ_of_gcd 34 50 84 2 17 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 84 (Polychromatic418967fa.accept_9_6_5_3_1_205 33
  50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 84 2 16 25 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 84 (accept_3_4 31 50
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 84 2 15 25 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 84
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 84 2 14 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 84 (Polychromatic418967fa.accept_15_12_5_9_1_3234 27 50 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 84 2 13 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 84 (accept_3_4 25 50 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 50 84 2 12 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 84 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 50 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 84 2 11 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 84 (Polychromatic418967fa.accept_13_8_11_6_1_1035
  21 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 84 2 10 25 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 84 (accept_3_4 19 50
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 84 2 9 25 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 50 84
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 50 84 2 8 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 50 84 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 50 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 84 2 7 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 84 (accept_3_4 13 50 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 50 84 2 6 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 50 84 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 50 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 84 2 5 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 84 (Polychromatic418967fa.accept_27_9_23_3_1_3271 9
  50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 84 2 4 25 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 84 (accept_3_4 7 50
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 84 2 3 25 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50 84
  (Polychromatic418967fa.accept_13_5_11_6_1_505 5 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 50 84 2 2 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 50 84 (Polychromatic418967fa.accept_15_3_5_9_1_764 3 50 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 84 2 1 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 84 (accept_3_4 1 50 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 84))))))))))))))))))))))))))))))))))) (allB_succ' 36 49 84 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 49 84 7 5 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 49 84 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 49 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 49 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 84 (accept_3_5 32 49 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 84 (Polychromatic418967fa.accept_11_9_5_7_1_815 31
  49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 84
  (Polychromatic418967fa.accept_13_4_10_6_1_989 30 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 84 (accept_3_5 29 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49 84
  7 4 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 49 84
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 27 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 84 (accept_3_5 26 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49
  84 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 49 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 49 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 84 (accept_3_5 23 49 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 49 84 (Polychromatic418967fa.accept_13_9_10_6_1_1028 22 49 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 49 84 7 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 49 84 (accept_3_5 20 49 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 49 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 84
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 84 (accept_3_5 17 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49
  84 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 49 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 49 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 49 84 7 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 49 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 49 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 84
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 84 (accept_3_5 11 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49
  84 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 49 84 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 49 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 84 (accept_3_5 8 49 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 49 84 7 1 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 49 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 49 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 84 (accept_3_5 5 49 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 84 (Polychromatic418967fa.accept_13_4_10_6_1_989 4 49 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 84 (Polychromatic418967fa.accept_10_3_9_4_1_960 3
  49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 84 (accept_3_5 2 49 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 49
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 84))))))))))))))))))))))))))))))))))))
  (allB_succ' 37 48 84 (Eq.refl Bool.true) (allA_succ_of_gcd 36 48 84 12 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 84 (Polychromatic418967fa.accept_15_5_3_9_1_283 35
  48 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 84 2 17 24 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 48 84 3 11 16 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 48 84 4 8 12 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 84
  (Polychromatic418967fa.accept_19_12_10_8_1_3270 31 48 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 84 6 5 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 84 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 48 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 84 4 7 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 48 84 3 9 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 48 84 2 13 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 84 (Polychromatic418967fa.accept_11_3_4_7_1_114 25 48 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 84 12 2 4 7 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 84
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 48 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 48 84 2 11 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 48 84 3 7 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 48 84 4 5 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 84 (Polychromatic418967fa.accept_10_9_8_4_1_970 19 48 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 84 6 3 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 84 (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 48 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 84 4 4 12 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 84 3 5 16 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 84 2 7 24 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 84
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 48 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 84 12 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 84 (Polychromatic418967fa.accept_17_11_14_16_1_1270 11 48 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 84 2 5 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 84 3 3 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 84 4 2 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 84 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 48 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 84 6 1 8 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 84
  (Polychromatic418967fa.accept_15_5_3_9_1_283 5 48 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 84 4 1 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 48 84 3 1 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 48 84 2 1 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 84 (Polychromatic418967fa.accept_13_1_9_6_1_146 1 48 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 84))))))))))))))))))))))))))))))))))))) (allB_succ' 38 47 84 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 47 84 (accept_3_4 37 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 47 84 (Polychromatic418967fa.accept_19_17_9_8_1_3269 36 47 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 84 (accept_3_4 34 47 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 84 (Polychromatic418967fa.accept_9_6_2_3_1_771 33
  47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 84
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 84 (accept_3_4 31 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47
  84 (Polychromatic418967fa.accept_16_14_15_4_1_3268 30 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 84 (Polychromatic418967fa.accept_17_12_13_16_1_3226 29 47 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 84 (accept_3_4 28 47 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 47 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 84
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 84 (accept_3_4 25 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47
  84 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 47 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 47 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 84 (accept_3_4 22 47 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 47 84 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 47 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 84 (Polychromatic418967fa.accept_17_3_13_16_1_2183
  20 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 84 (accept_3_4 19 47
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 84
  (Polychromatic418967fa.accept_19_18_9_8_1_3267 18 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 47 84 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 47 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 84 (accept_3_4 16 47 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 47 84 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 47 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 14
  47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 84 (accept_3_4 13 47 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 84 (Polychromatic418967fa.accept_10_2_7_4_1_967 12
  47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 84
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 84 (accept_3_4 10 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47
  84 (Polychromatic418967fa.accept_17_9_13_16_1_3266 9 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 84 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 47 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 84 (accept_3_4 7 47 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 84 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 47 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 47
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 84 (accept_3_4 4 47 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 47
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 84
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 84 (accept_3_4 1 47 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  84)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 46 84 (Eq.refl Bool.true) (allA_succ_of_gcd 38 46 84 2 19 23
  42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 84
  (Polychromatic418967fa.accept_15_7_1_9_1_1500 37 46 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 84 2 18 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 84 (accept_3_5 35 46 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 84
  2 17 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46
  84 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 46 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 46 84 2 16 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 46 84 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 46 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 84 2 15 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 84 (accept_3_5 29 46 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 46 84 2 14 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 84 (Polychromatic418967fa.accept_13_1_7_6_1_142 27 46 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 84 2 13 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 25
  46 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 84 2 12 23 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 84 (accept_3_5 23 46
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 84 2 11 23 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 84
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 46 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 84 2 10 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 84 (Polychromatic418967fa.accept_25_19_21_9_1_3265 19 46 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 84 2 9 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 84 (accept_3_5 17 46 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 84 2 8 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 84 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 46 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 84 2 7 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 84 (Polychromatic418967fa.accept_9_4_1_3_1_190 13
  46 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 84 2 6 23 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 84 (accept_3_5 11 46
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 84 2 5 23 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 84
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 46 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 84 2 4 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 46 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 84 2 3 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 84 (accept_3_5 5 46 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 84 2 2 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 84 (Polychromatic418967fa.accept_31_3_15_22_1_3264 3 46 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 84 2 1 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 84 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 46
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 84)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 45 84 (Eq.refl Bool.true) (allA_succ_of_gcd 39 45 84 3 13 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 84 (Polychromatic418967fa.accept_16_6_13_4_1_643 38
  45 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 84
  (Polychromatic418967fa.accept_19_18_7_8_1_2112 37 45 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 45 84 3 12 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 45 84 (Polychromatic418967fa.accept_18_17_9_12_1_2160 35 45 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 84 (Polychromatic418967fa.accept_18_16_9_12_1_1182 34 45 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 84 3 11 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 84
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 32 45 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 84 (Polychromatic418967fa.accept_10_1_5_4_1_276 31 45 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 84 3 10 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 84 (Polychromatic418967fa.accept_10_9_5_4_1_966 29 45 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 84
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 45 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 84 3 9 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 84 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 45 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 45 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 84 3 8 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 84
  (Polychromatic418967fa.accept_16_7_13_4_1_1348 23 45 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 84 (Polychromatic418967fa.accept_16_6_13_4_1_643 22 45 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 84 3 7 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 84 (Polychromatic418967fa.accept_19_1_7_8_1_3262 20 45 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 84
  (Polychromatic418967fa.accept_10_9_5_4_1_966 19 45 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 45 84 3 6 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 45 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 45 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 84 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 45 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 84 3 5 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 84
  (Polychromatic418967fa.accept_17_14_11_16_1_3261 14 45 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 84 (Polychromatic418967fa.accept_22_13_1_18_1_3260 13 45 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 84 3 4 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 84 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 45 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 84
  (Polychromatic418967fa.accept_18_10_9_12_1_3259 10 45 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 45 84 3 3 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 84 (Polychromatic418967fa.accept_16_8_13_4_1_3258 8 45 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 84 (Polychromatic418967fa.accept_16_7_13_4_1_1348 7 45 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 84 3 2 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 84
  (Polychromatic418967fa.accept_17_5_11_16_1_3257 5 45 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 84 (Polychromatic418967fa.accept_18_4_9_12_1_1175 4 45 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 84 3 1 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 84 (Polychromatic418967fa.accept_20_2_5_4_1_3256 2 45 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 84
  (Polychromatic418967fa.accept_8_1_5_4_1_388 1 45 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 84)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 44 84 (Eq.refl Bool.true) (allA_succ_of_gcd 40
  44 84 4 10 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 44 84 (Polychromatic418967fa.accept_16_7_12_4_1_1347 39 44 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 44 84 2 19 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 44 84 (accept_3_4 37 44 84 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 44 84 4 9 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 44 84 (Polychromatic418967fa.accept_15_5_14_9_1_274 35 44 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 84 2 17 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 84 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 44 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 84 4 8 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 84 (accept_3_4 31 44 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 84 2 15 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 29
  44 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 84 4 7 11 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 84
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 44 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 84 2 13 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 44 84 (accept_3_4 25 44 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 84
  4 6 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44
  84 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 44 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 84 2 11 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 84 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 44 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 84 4 5 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 84 (accept_3_4 19 44 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 44 84 2 9 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 44 84 (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 44 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 84 4 4 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 84 (Polychromatic418967fa.accept_9_6_8_3_1_183 15
  44 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 84 2 7 22 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 84 (accept_3_4 13 44
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 84 4 3 11 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 84
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 44 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 44 84 2 5 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 44 84 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 44 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 84 4 2 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 84 (accept_3_4 7 44 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 44 84 2 3 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 44 84 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 44 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 84 4 1 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 84 (Polychromatic418967fa.accept_13_3_5_6_1_3192 3
  44 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 84 2 1 22 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 84 (accept_3_4 1 44
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 84))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 43
  84 (Eq.refl Bool.true) (allA_succ_of_accept 41 43 84 (accept_3_5 41 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 43 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 43 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 43 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 84 (accept_3_5 38 43 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 37
  43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 84
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 84 (accept_3_5 35 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43
  84 (Polychromatic418967fa.accept_15_4_13_9_1_3197 34 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 84 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 43 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 84 (accept_3_5 32 43 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 43 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 84
  (Polychromatic418967fa.accept_17_13_9_16_1_3254 30 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 84 (accept_3_5 29 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43
  84 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 43 84 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 43 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 84 (accept_3_5 26 43 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 43 84 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 43 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 84 (Polychromatic418967fa.accept_9_6_7_3_1_436 24
  43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 84 (accept_3_5 23 43 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 22
  43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 84
  (Polychromatic418967fa.accept_18_3_7_12_1_1196 21 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 84 (accept_3_5 20 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43
  84 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 43 84 (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 43 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 84 (accept_3_5 17 43 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 43 84 (Polychromatic418967fa.accept_19_16_5_8_1_3253 16 43 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 15
  43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 84 (accept_3_5 14 43 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 13
  43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 84
  (Polychromatic418967fa.accept_16_12_11_4_1_1359 12 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 84 (accept_3_5 11 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43
  84 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 43 84 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 43 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 84 (accept_3_5 8 43 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 43 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 43 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 84 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 43
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 84 (accept_3_5 5 43 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 43
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 84
  (Polychromatic418967fa.accept_11_3_10_7_1_129 3 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 84 (accept_3_5 2 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 84
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 43 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 84)))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 84 (allA_succ_of_accept 41 42 84
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 42 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 84 2 20 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 42 84 3 13 14 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 42 84 2 19 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 42 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 84 6 6 7 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 84 7 5 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 42 84 2 17 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 42 84 3 11 14 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 42 84 2 16 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 42 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 84 6 5 7 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 84
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 42 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 84 14 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 42 84 3 9 14 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 42 84 2 13 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 42 84 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 42 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 84 6 4 7 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 42 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 84 2 11 21 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 84 21 1 2 4 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 84 2 10 21 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 84
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 42 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 84 6 3 7 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 84 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 42 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 84 2 8 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 42 84 3 5 14 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 84 14 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 42 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 84 6 2 7 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 84
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 42 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 84 2 5 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 42 84 3 3 14 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 42 84 2 4 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 42 84 7 1 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 42 84 6 1 7 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 42 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 84 2 2 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 84 3 1 14 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 84 2 1 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 42 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 84))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 41 84 (allA_succ_of_accept 40 41 84 (accept_3_4 40 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 41 84 (Polychromatic418967fa.accept_24_15_17_12_1_662 39 41 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 84 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 41 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 84 (accept_3_4 37 41 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 84 (Polychromatic418967fa.accept_13_10_2_6_1_1044
  36 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 84
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 84 (accept_3_4 34 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41
  84 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 84 (Polychromatic418967fa.accept_15_2_11_9_1_263 32 41 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 84 (accept_3_4 31 41 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 84 (Polychromatic418967fa.accept_13_4_2_6_1_1043 30 41 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 29
  41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 84 (accept_3_4 28 41 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 84 (Polychromatic418967fa.accept_10_7_1_4_1_1447
  27 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 84
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 84 (accept_3_4 25 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41
  84 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 41 84 (Polychromatic418967fa.accept_13_10_2_6_1_1044 23 41 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 84 (accept_3_4 22 41 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 41 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 41 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 84 (Polychromatic418967fa.accept_9_2_5_3_1_37 20
  41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 84 (accept_3_4 19 41 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 84
  (Polychromatic418967fa.accept_24_18_17_12_1_3252 18 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 41 84 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 41 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 84 (accept_3_4 16 41 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 41 84 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 41 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 84 (Polychromatic418967fa.accept_13_1_2_6_1_515 14
  41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 84 (accept_3_4 13 41 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 84 (Polychromatic418967fa.accept_13_12_2_6_1_2396
  12 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 84
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 84 (accept_3_4 10 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41
  84 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 41 84 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 41 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 84 (accept_3_4 7 41 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 41 84 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 41 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 41
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 84 (accept_3_4 4 41 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 84 (Polychromatic418967fa.accept_17_3_7_16_1_3251 3
  41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 84
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 41 84 (accept_3_4 1 41 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41
  84))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 84 (allA_succ_of_accept 39 40 84
  (Polychromatic418967fa.accept_16_7_8_4_1_689 39 40 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 84 2 19 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 40 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 84 4 9 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 84 (accept_3_5 35 40 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 40 84 2 17 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 40 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 40 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 84 4 8 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 84 (Polychromatic418967fa.accept_13_5_1_6_1_2367 31
  40 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 84 2 15 20 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 84 (accept_3_5 29 40
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 84 4 7 10 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40 84
  (Polychromatic418967fa.accept_15_12_10_9_1_798 27 40 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 40 84 2 13 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 40 84 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 40 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 84 4 6 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 84 (accept_3_5 23 40 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 40 84 2 11 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 40 84 (Polychromatic418967fa.accept_13_8_1_6_1_997 21 40 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 84 4 5 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 19
  40 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 84 2 9 20 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 84 (accept_3_5 17 40
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 84 4 4 10 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 40 84
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 40 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 40 84 2 7 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 40 84 (Polychromatic418967fa.accept_16_13_8_4_1_3250 13 40 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 84 4 3 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 84 (accept_3_5 11 40 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 40 84 2 5 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 40 84 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 40 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 84 4 2 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 84 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 40
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 84 2 3 20 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 84 (accept_3_5 5 40
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 84 4 1 10 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 84
  (Polychromatic418967fa.accept_13_3_1_6_1_509 3 40 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 40 84 2 1 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 40 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 40 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 40 84)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 84
  (allA_succ_of_accept 38 39 84 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 39 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 84 (Polychromatic418967fa.accept_18_1_3_12_1_467 37 39 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 84 3 12 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 84
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 39 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 39 84 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 39 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 39 84 3 11 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 39 84 (Polychromatic418967fa.accept_18_14_3_12_1_3249 32 39 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 84
  (Polychromatic418967fa.accept_18_13_3_12_1_3207 31 39 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 39 84 3 10 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 39 84 (Polychromatic418967fa.accept_16_13_7_4_1_3248 29 39 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 84 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 39 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 84 3 9 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 84
  (Polychromatic418967fa.accept_18_8_3_12_1_3247 26 39 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 84 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 39 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 84 3 8 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 84 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 39 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 84
  (Polychromatic418967fa.accept_20_2_19_4_1_3246 22 39 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 39 84 3 7 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 39 84 (Polychromatic418967fa.accept_18_2_3_12_1_1155 20 39 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 39 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 84 3 6 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 84
  (Polychromatic418967fa.accept_23_17_16_15_1_3245 17 39 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 84 (Polychromatic418967fa.accept_19_16_1_8_1_3244 16 39 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 84 3 5 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 84 (Polychromatic418967fa.accept_16_14_7_4_1_3243 14 39 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 84
  (Polychromatic418967fa.accept_10_3_9_4_1_960 13 39 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 39 84 3 4 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 39 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 39 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 84 (Polychromatic418967fa.accept_22_10_17_18_1_3242 10 39
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 84 3 3 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 84
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 39 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 84 (Polychromatic418967fa.accept_18_7_3_12_1_3241 7 39 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 84 3 2 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 84 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 39 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 84
  (Polychromatic418967fa.accept_17_4_5_16_1_3240 4 39 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 39 84 3 1 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 39 84 (Polychromatic418967fa.accept_17_2_5_16_1_1264 2 39 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 84 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 39 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 84)))))))))))))))))))))))))))))))))))))))
  (allB_succ 38 84 (allA_succ_of_accept 37 38 84 (accept_3_4 37 38 84 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 38 84 2 18 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 38 84 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 38 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 38 84 2 17 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 38 84 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 38 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 84 2 16 19 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 84 (accept_3_4 31 38 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 84 2 15 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 84 (Polychromatic418967fa.accept_10_9_8_4_1_970 29
  38 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 38 84 2 14 19 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 38 84
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 38 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 38 84 2 13 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 38 84 (accept_3_4 25 38 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 84
  2 12 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38
  84 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 38 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 38 84 2 11 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 38 84 (Polychromatic418967fa.accept_16_5_6_4_1_3211 21 38 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 84 2 10 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 84 (accept_3_4 19 38 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 38 84 2 9 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 38 84 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 38 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 84 2 8 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 84 (Polychromatic418967fa.accept_9_6_2_3_1_771 15
  38 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 84 2 7 19 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 84 (accept_3_4 13 38
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 84 2 6 19 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 84
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 11 38 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 84 2 5 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 84 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 38 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 84 2 4 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 84 (accept_3_4 7 38 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 84 2 3 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 38 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 84 2 2 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 84 (Polychromatic418967fa.accept_15_3_8_9_1_795 3 38
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 84 2 1 19 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 84 (accept_3_4 1 38
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 84)))))))))))))))))))))))))))))))))))))) (allB_succ 37 84
  (allA_succ_of_accept 36 37 84 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 37 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 84 (accept_3_5 35 37 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 37 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 33
  37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 84 (accept_3_5 32 37 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 84 (Polychromatic418967fa.accept_9_4_1_3_1_190 31
  37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 84
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 84 (accept_3_5 29 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37
  84 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 84 (Polychromatic418967fa.accept_20_7_17_4_1_3239 27 37 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 84 (accept_3_5 26 37 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 37 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 84
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 84 (accept_3_5 23 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37
  84 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 37 84 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 37 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 84 (accept_3_5 20 37 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 37 84 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 37 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 84 (Polychromatic418967fa.accept_13_5_11_6_1_505
  18 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 84 (accept_3_5 17 37
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 84 (Polychromatic418967fa.accept_9_7_1_3_1_443
  16 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 84
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 84 (accept_3_5 14 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37
  84 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 84 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 37 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 84 (accept_3_5 11 37 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 84 (Polychromatic418967fa.accept_19_10_18_8_1_3238 10 37 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 37
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 84 (accept_3_5 8 37 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 37
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 84
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 84 (accept_3_5 5 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 84
  (Polychromatic418967fa.accept_9_4_1_3_1_190 4 37 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 84 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 37 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 84 (accept_3_5 2 37 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 37 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 84))))))))))))))))))))))))))))))))))))) (allB_succ 36 84
  (allA_succ_of_accept 35 36 84 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 36 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 84 2 17 18 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 84 3 11 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 84 4 8 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 84 (Polychromatic418967fa.accept_13_5_10_6_1_2361 31 36 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 84 6 5 6 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 84
  (Polychromatic418967fa.accept_13_3_10_6_1_2382 29 36 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 84 4 7 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 84 3 9 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 84 2 13 18 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 84 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 36 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 84 12 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 84 (Polychromatic418967fa.accept_19_4_17_8_1_2103 23 36 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 84 2 11 18 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 84 3 7 12 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 84 4 5 9 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 84
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 36 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 84 6 3 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 84 (Polychromatic418967fa.accept_13_4_10_6_1_989 17 36 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 84 4 4 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 84 3 5 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 84 2 7 18 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 84 (Polychromatic418967fa.accept_22_13_14_18_1_3237 13 36 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 84 12 1 3 7 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 84
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 36 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 84 2 5 18 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 36 84 3 3 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 36 84 4 2 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 84 (Polychromatic418967fa.accept_22_7_14_18_1_3235 7 36 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 84 6 1 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 84 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 36 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 84 4 1 9 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 84 3 1 12 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 84 2 1 18 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 84
  (Polychromatic418967fa.accept_15_1_6_9_1_254 1 36 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 84)))))))))))))))))))))))))))))))))))) (allB_succ 35 84 (allA_succ_of_accept 34 35 84 (accept_3_4 34 35
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 84 (Polychromatic418967fa.accept_9_6_8_3_1_183
  33 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 84
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 84 (accept_3_4 31 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35
  84 (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 35 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 35 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 35 84 7 4 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 35 84 (Polychromatic418967fa.accept_13_1_9_6_1_146 27 35 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 84
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 84 (accept_3_4 25 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35
  84 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 35 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 84 (accept_3_4 22 35 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 35 84 7 3 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 35 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 35 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 84 (accept_3_4 19 35 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 84 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 35 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 84
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 84 (accept_3_4 16 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35
  84 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 35 84 7 2 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 35 84 (accept_3_4 13 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35
  84 (Polychromatic418967fa.accept_15_12_5_9_1_3234 12 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 35 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 84 (accept_3_4 10 35 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 84 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 35 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 84
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 35 84 7 1 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 35 84 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 35 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 84 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 35 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 84 (accept_3_4 4 35 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 84 (Polychromatic418967fa.accept_13_3_9_6_1_502 3 35 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 84
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 84 (accept_3_4 1 35 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  84))))))))))))))))))))))))))))))))))) (allB_succ 34 84 (allA_succ_of_accept 33 34 84
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 34 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 84 2 16 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 34 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 84 2 15 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 84 (accept_3_5 29 34 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 34 84 2 14 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 84 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 34 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 84 2 13 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 84 (Polychromatic418967fa.accept_15_10_4_9_1_3203
  25 34 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 84 2 12 17 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 84 (accept_3_5 23 34
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 84 2 11 17 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 84
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 21 34 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 84 2 10 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 34 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 84 2 9 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 84 (accept_3_5 17 34 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 84 2 8 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 84 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 34 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 84 2 7 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 34
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 84 2 6 17 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 84 (accept_3_5 11 34
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 84 2 5 17 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 84
  (Polychromatic418967fa.accept_18_9_16_12_1_1143 9 34 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 84 2 4 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 84 (Polychromatic418967fa.accept_19_7_15_8_1_1089 7 34 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 84 2 3 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 84 (accept_3_5 5 34 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 84 2 2 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 84 (Polychromatic418967fa.accept_19_3_15_8_1_3232 3 34 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 84 2 1 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 34
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 84))))))))))))))))))))))))))))))))))
  (allB_succ 33 84 (allA_succ_of_accept 32 33 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 33 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 31
  33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 84 3 10 11 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 84
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 33 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 84 3 9 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 84 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 33 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 84
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 33 84 3 8 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 33 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 33 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 33 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 84 3 7 11 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 84
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 33 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 84 3 6 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 84 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 33 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 84
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 33 84 3 5 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 33 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 33 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 33 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 84 3 4 11 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 84
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 33 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 84 3 3 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 84 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 33 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 84
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 33 84 3 2 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 33 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 33 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 33 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 84 3 1 11 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 84
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 33 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 33 84))))))))))))))))))))))))))))))))) (allB_succ 32 84 (allA_succ_of_accept
  31 32 84 (accept_3_4 31 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 84 2 15 16 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 84
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 84 4 7 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 84 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 32 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 84 2 13 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 84 (accept_3_4 25 32 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 32 84 4 6 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 32 84 (Polychromatic418967fa.accept_15_8_2_9_1_3200 23 32 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 84 2 11 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 84 (Polychromatic418967fa.accept_17_4_15_16_1_3231
  21 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 84 4 5 8 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 84 (accept_3_4 19 32
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 84 2 9 16 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32 84
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 32 84 4 4 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 32 84 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 32 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 84 2 7 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 84 (accept_3_4 13 32 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 32 84 4 3 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 32 84 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 32 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 84 2 5 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 84 (Polychromatic418967fa.accept_22_9_10_18_1_3230 9
  32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 84 4 2 8 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 84 (accept_3_4 7 32
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 84 2 3 16 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 84
  (Polychromatic418967fa.accept_19_5_13_8_1_3229 5 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 84 4 1 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 84 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 32 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 84 2 1 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 84 (accept_3_4 1 32 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 84)))))))))))))))))))))))))))))))) (allB_succ 31 84 (allA_succ_of_accept 30 31 84
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 30 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 84 (accept_3_5 29 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31
  84 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 31 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 31 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 84 (accept_3_5 26 31 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 31 84 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 31 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 24
  31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 84 (accept_3_5 23 31 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 84 (Polychromatic418967fa.accept_15_7_1_9_1_1500
  22 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 84
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 84 (accept_3_5 20 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31
  84 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 84 (Polychromatic418967fa.accept_23_18_8_15_1_3228 18 31 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 84 (accept_3_5 17 31 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 84 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 31 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 84 (accept_3_5 14 31 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 84 (Polychromatic418967fa.accept_11_2_9_7_1_124 13
  31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 84
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 12 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 84 (accept_3_5 11 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31
  84 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 31 84 (Polychromatic418967fa.accept_24_9_7_12_1_3227 9 31 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 84 (accept_3_5 8 31 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 31 84 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 31 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 31
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 84 (accept_3_5 5 31 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 84 (Polychromatic418967fa.accept_13_4_5_6_1_3201 4
  31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 84
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 84 (accept_3_5 2 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 84
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 84))))))))))))))))))))))))))))))) (allB_succ 30 84 (allA_succ_of_accept 29 30 84
  (Polychromatic418967fa.accept_17_12_13_16_1_3226 29 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 84 2 14 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 30 84 3 9 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 30 84 2 13 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 84 (Polychromatic418967fa.accept_16_9_14_4_1_3225 25 30 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 84 6 4 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 84 (Polychromatic418967fa.accept_13_10_4_6_1_3224 23 30 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 84 2 11 15 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 30 84 3 7 10 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 84 2 10 15 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 84
  (Polychromatic418967fa.accept_22_19_8_18_1_3223 19 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 84 6 3 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 84 (Polychromatic418967fa.accept_16_1_14_4_1_3220 17 30 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 84 2 8 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 84 3 5 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 84 2 7 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 84 (Polychromatic418967fa.accept_23_13_7_15_1_3222 13 30 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 84 6 2 5 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 84
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 84 2 5 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 30 84 3 3 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 30 84 2 4 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 84 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 30 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 84 6 1 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 84 (Polychromatic418967fa.accept_13_5_4_6_1_2371 5 30 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 84 2 2 15 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 30 84 3 1 10 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 30 84 2 1 15 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 84
  (Polychromatic418967fa.accept_16_1_14_4_1_3220 1 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 84)))))))))))))))))))))))))))))) (allB_succ 29 84 (allA_succ_of_accept 28 29 84 (accept_3_4 28 29 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 84 (Polychromatic418967fa.accept_13_1_3_6_1_158 27
  29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 84
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 84 (accept_3_4 25 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29
  84 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 29 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 29 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 84 (accept_3_4 22 29 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 29 84 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 29 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 84 (Polychromatic418967fa.accept_15_5_14_9_1_274
  20 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 84 (accept_3_4 19 29
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 84 (Polychromatic418967fa.accept_10_8_9_4_1_961
  18 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 84
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 84 (accept_3_4 16 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29
  84 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 29 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 84 (accept_3_4 13 29 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 84 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 29 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 84
  (Polychromatic418967fa.accept_17_11_12_16_1_3219 11 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 84 (accept_3_4 10 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29
  84 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 84 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 29 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 84 (accept_3_4 7 29 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 84 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 29 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 29
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 84 (accept_3_4 4 29 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 84 (Polychromatic418967fa.accept_10_3_9_4_1_960 3
  29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 84
  (Polychromatic418967fa.accept_19_2_10_8_1_3218 2 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 84 (accept_3_4 1 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  84))))))))))))))))))))))))))))) (allB_succ 28 84 (allA_succ_of_accept 27 28 84
  (Polychromatic418967fa.accept_13_1_2_6_1_515 27 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 84 2 13 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 28 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 84 4 6 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 84 (accept_3_5 23 28 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 84 2 11 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 28 84 7 3 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 28 84 4 5 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 28 84 (Polychromatic418967fa.accept_10_9_8_4_1_970 19 28 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 84 2 9 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 84 (accept_3_5 17 28 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 84 4 4 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 28 84 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 28 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 84 14 1 2 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 84
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 28 84 4 3 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 28 84 (accept_3_5 11 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 84
  2 5 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 84
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 84 4 2 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 28 84 7 1 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 28 84 2 3 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 84 (accept_3_5 5 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 84 4
  1 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 84
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 3 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 84 2 1 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 84 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 28 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 84)))))))))))))))))))))))))))) (allB_succ 27 84 (allA_succ_of_accept 26
  27 84 (Polychromatic418967fa.accept_17_9_10_16_1_3217 26 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 84 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 27 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 84 3 8 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 23
  27 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 84
  (Polychromatic418967fa.accept_10_2_7_4_1_967 22 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 84 3 7 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 84 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 27 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 84 (Polychromatic418967fa.accept_15_4_12_9_1_773 19 27 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 84 3 6 9 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 84
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 17 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 84 (Polychromatic418967fa.accept_13_3_1_6_1_509 16 27 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 84 3 5 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 84 (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 27 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 84
  (Polychromatic418967fa.accept_10_3_7_4_1_584 13 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 84 3 4 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 84 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 27 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 84 (Polychromatic418967fa.accept_15_10_12_9_1_776 10 27 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 84 3 3 9 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 84
  (Polychromatic418967fa.accept_13_8_1_6_1_997 8 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 27 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 84 3 2 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 84 (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 27 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 84
  (Polychromatic418967fa.accept_15_4_12_9_1_773 4 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 84 3 1 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 84 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 27 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 84 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 27 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 84))))))))))))))))))))))))))) (allB_succ 26
  84 (allA_succ_of_accept 25 26 84 (accept_3_4 25 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  84 2 12 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 84 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 84 2 11 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 26 84 (Polychromatic418967fa.accept_15_6_11_9_1_3215 21 26 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 84 2 10 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 84 (accept_3_4 19 26 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 84 2 9 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 26 84 (Polychromatic418967fa.accept_15_2_11_9_1_263 17 26 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 84 2 8 13 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 84
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 84 2 7 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 84 (accept_3_4 13 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 84
  2 6 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26
  84 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 26 84 2 5 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 26 84 (Polychromatic418967fa.accept_19_9_7_8_1_3214 9 26 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 84 2 4 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 84 (accept_3_4 7 26 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 26 84 2 3 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 26 84 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 26 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 84 2 2 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 84 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 26
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 84 2 1 13 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 84 (accept_3_4 1 26
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 84)))))))))))))))))))))))))) (allB_succ 25 84
  (allA_succ_of_accept 24 25 84 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 25 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 84 (accept_3_5 23 25 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 25 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 21
  25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 84 (accept_3_5 20 25 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 19
  25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 84
  (Polychromatic418967fa.accept_13_5_12_6_1_508 18 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 84 (accept_3_5 17 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25
  84 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 25 84 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 25 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 84 (accept_3_5 14 25 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 25 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 25 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 84 (Polychromatic418967fa.accept_15_12_10_9_1_798
  12 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 84 (accept_3_5 11 25
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 84 (Polychromatic418967fa.accept_9_1_7_3_1_41
  10 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 84
  (Polychromatic418967fa.accept_10_9_5_4_1_966 9 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 84 (accept_3_5 8 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 84
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 84 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 25 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 84 (accept_3_5 5 25 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 25 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 84 (Polychromatic418967fa.accept_15_3_10_9_1_769 3
  25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 84 (accept_3_5 2 25 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 25
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 84))))))))))))))))))))))))) (allB_succ 24
  84 (allA_succ_of_accept 23 24 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 24 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 84 2 11 12 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 84 3 7 8 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 84 4 5 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 24 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 84 6 3 4 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 84
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 24 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 84 4 4 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 84 3 5 8 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 84 2 7 12 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 24 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 84 12 1 2 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 84 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 24 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 84 2 5 12 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 84 3 3 8 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 84 4 2 6 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 84
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 24 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 84 6 1 4 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 84 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 24 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 84 4 1 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 84 3 1 8 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 84 2 1 12 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 24 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 84)))))))))))))))))))))))) (allB_succ 23 84
  (allA_succ_of_accept 22 23 84 (accept_3_4 22 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23
  84 (Polychromatic418967fa.accept_20_1_3_4_1_3213 21 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 84 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 23 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 84 (accept_3_4 19 23 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 84 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 23 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 84 (Polychromatic418967fa.accept_9_8_5_3_1_777 17
  23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 84 (accept_3_4 16 23 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 84 (Polychromatic418967fa.accept_9_6_5_3_1_205 15
  23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 84
  (Polychromatic418967fa.accept_15_14_8_9_1_1452 14 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 84 (accept_3_4 13 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  84 (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 23 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 84 (accept_3_4 10 23 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 84 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 23 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 84
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 84 (accept_3_4 7 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 84
  (Polychromatic418967fa.accept_9_6_5_3_1_205 6 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 84 (Polychromatic418967fa.accept_13_5_10_6_1_2361 5 23 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 84 (accept_3_4 4 23 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 23 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 84 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 23
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 84 (accept_3_4 1 23 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 84))))))))))))))))))))))) (allB_succ 22 84 (allA_succ_of_accept
  21 22 84 (Polychromatic418967fa.accept_16_5_6_4_1_3211 21 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 22 84 2 10 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 22 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 22 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 84 2 9 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 84 (accept_3_5 17 22 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 84 2 8 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 22 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 22 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 84 2 7 11 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 84
  (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 22 84 2 6 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 22 84 (accept_3_5 11 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 84
  2 5 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 84
  (Polychromatic418967fa.accept_18_9_4_12_1_3209 9 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 84 2 4 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 84 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 22 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 84 2 3 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 84 (accept_3_5 5 22 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 84 2 2 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 84 (Polychromatic418967fa.accept_13_3_9_6_1_502 3 22 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 84 2 1 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 22
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 84)))))))))))))))))))))) (allB_succ 21 84
  (allA_succ_of_accept 20 21 84 (Polychromatic418967fa.accept_17_3_4_16_1_3208 20 21 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 84 (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 21 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 84 3 6 7 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 84
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 21 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 84 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 21 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 84 3 5 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 21 84 7 2 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 84 (Polychromatic418967fa.accept_18_13_3_12_1_3207 13 21 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 84 3 4 7 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 84
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 21 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 84 (Polychromatic418967fa.accept_19_10_2_8_1_3206 10 21 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 84 3 3 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 84 (Polychromatic418967fa.accept_16_8_5_4_1_674 8 21 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 84 7 1 3 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 21 84 3 2 7 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 84
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 21 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 84 (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 21 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 84 3 1 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 84 (Polychromatic418967fa.accept_13_2_8_6_1_2390 2 21 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 84
  (Polychromatic418967fa.accept_8_1_5_4_1_388 1 21 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 84))))))))))))))))))))) (allB_succ 20 84 (allA_succ_of_accept 19 20 84 (accept_3_4 19 20 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 84 2 9 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 84 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 20 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 20 84 4 4 5 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 20 84
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 20 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 20 84 2 7 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 20 84 (accept_3_4 13 20 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 84
  4 3 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20 84
  (Polychromatic418967fa.accept_15_11_5_9_1_3205 11 20 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 84 2 5 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 84 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 20 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 84 4 2 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 84 (accept_3_4 7 20 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 20 84 2 3 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 20 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 20 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 20 84 4 1 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 20 84 (Polychromatic418967fa.accept_15_3_5_9_1_764 3 20
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 84 2 1 10 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 84 (accept_3_4 1 20
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 84)))))))))))))))))))) (allB_succ 19 84 (allA_succ_of_accept
  18 19 84 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 84 (accept_3_5 17 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 19 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 19 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 84 (accept_3_5 14 19 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 84 (Polychromatic418967fa.accept_9_4_1_3_1_190 13
  19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 84
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 12 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 84 (accept_3_5 11 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19
  84 (Polychromatic418967fa.accept_15_10_4_9_1_3203 10 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 84 (Polychromatic418967fa.accept_20_9_19_4_1_3202 9 19 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 84 (accept_3_5 8 19 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 19 84 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 19 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 84 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 19
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 84 (accept_3_5 5 19 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 84 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 19
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 84
  (Polychromatic418967fa.accept_10_3_9_4_1_960 3 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 84 (accept_3_5 2 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 84
  (Polychromatic418967fa.accept_16_1_3_4_1_665 1 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 19 84))))))))))))))))))) (allB_succ 18 84 (allA_succ_of_accept 17 18 84
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 18 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 84 2 8 9 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 18 84 3 5 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 18 84 2 7 9 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 84 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 18 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 84 6 2 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 84 (Polychromatic418967fa.accept_13_11_5_6_1_519 11 18 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 84 2 5 9 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 18 84 3 3 6 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 18 84 2 4 9 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 84
  (Polychromatic418967fa.accept_19_7_18_8_1_1067 7 18 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 84 6 1 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 84 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 18 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 84 2 2 9 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 84 3 1 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 84 2 1 9 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 84 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 18 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 84)))))))))))))))))) (allB_succ 17 84
  (allA_succ_of_accept 16 17 84 (accept_3_4 16 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17
  84 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 84 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 17 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 84 (accept_3_4 13 17 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 84 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 17 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 11
  17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 84 (accept_3_4 10 17 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 84 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9
  17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 84
  (Polychromatic418967fa.accept_15_8_2_9_1_3200 8 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 84 (accept_3_4 7 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 84
  (Polychromatic418967fa.accept_9_6_8_3_1_183 6 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 84 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 17 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 84 (accept_3_4 4 17 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 84 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 17 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 84 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 17
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 84 (accept_3_4 1 17 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 84))))))))))))))))) (allB_succ 16 84 (allA_succ_of_accept 15 16
  84 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 16 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 84 2 7 8 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 84 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 16 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 84 4 3 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 84 (accept_3_5 11 16 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 84 2 5 8 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 84 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 16 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 84 4 2 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 84 (Polychromatic418967fa.accept_15_7_1_9_1_1500 7
  16 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 84 2 3 8 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 84 (accept_3_5 5 16
  84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 84 4 1 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 84 (Polychromatic418967fa.accept_25_3_16_9_1_3199 3
  16 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 84 2 1 8 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 84
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 16 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 84)))))))))))))))) (allB_succ 15 84 (allA_succ_of_accept 14 15 84
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 15 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 84 3 4 5 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 15 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 84
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 84 3 3 5 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 84 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 15 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 84 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 15 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 84 3 2 5 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 84
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 84 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 15 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 84 3 1 5 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 84 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 15 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 84
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 84))))))))))))))) (allB_succ 14 84 (allA_succ_of_accept 13 14 84 (accept_3_4 13 14 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 84 2 6 7 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 14 84 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 14 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 84 2 5 7 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 84
  (Polychromatic418967fa.accept_13_9_1_6_1_510 9 14 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 84 2 4 7 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 14 84 7 1 2 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 14 84 2 3 7 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 14 84 (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 14 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 84 2 2 7 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 84 (Polychromatic418967fa.accept_13_3_1_6_1_509 3 14 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 84 2 1 7 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 84 (accept_3_4 1 14 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 14 84)))))))))))))) (allB_succ 13 84 (allA_succ_of_accept 12 13 84
  (Polychromatic418967fa.accept_16_12_13_4_1_3198 12 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 84 (accept_3_5 11 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  84 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 13 84 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 13 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 84 (accept_3_5 8 13 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 84 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 13 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 84 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 13
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 84 (accept_3_5 5 13 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 84 (Polychromatic418967fa.accept_15_4_13_9_1_3197 4
  13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 84
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 3 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 84 (accept_3_5 2 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 84
  (Polychromatic418967fa.accept_8_1_5_4_1_388 1 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 84))))))))))))) (allB_succ 12 84 (allA_succ_of_accept 11 12 84
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 12 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 84 2 5 6 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 12 84 3 3 4 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 12 84 4 2 3 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 84 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 12 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 84 6 1 2 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 84 (Polychromatic418967fa.accept_13_5_12_6_1_508 5 12 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 84 4 1 3 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 84 3 1 4 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 84 2 1 6 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 84
  (Polychromatic418967fa.accept_16_1_12_4_1_695 1 12 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 84)))))))))))) (allB_succ 11 84 (allA_succ_of_accept 10 11 84 (accept_3_4 10 11 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 84 (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 11 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 84
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 11 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 84 (accept_3_4 7 11 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 84
  (Polychromatic418967fa.accept_9_6_2_3_1_771 6 11 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 84 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 11 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 84 (accept_3_4 4 11 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 84 (Polychromatic418967fa.accept_19_3_11_8_1_3193 3 11 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 84 (Polychromatic418967fa.accept_15_2_11_9_1_263 2
  11 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 84 (accept_3_4 1 11 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 84))))))))))) (allB_succ 10 84 (allA_succ_of_accept 9 10 84
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 10 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 84 2 4 5 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 84 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 10 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 84 2 3 5 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 84 (accept_3_5 5 10 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 84 2 2 5 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 84 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 10 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 84 2 1 5 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 84 (Polychromatic418967fa.accept_15_1_10_9_1_1495 1
  10 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 84)))))))))) (allB_succ 9 84
  (allA_succ_of_accept 8 9 84 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 9 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 84 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 9 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 84 3 2 3 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 84
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 9 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 84 (Polychromatic418967fa.accept_13_4_9_6_1_2376 4 9 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 84 3 1 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 84 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 9 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 84
  (Polychromatic418967fa.accept_13_1_9_6_1_146 1 9 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 84))))))))) (allB_succ 8 84 (allA_succ_of_accept 7 8 84 (accept_3_4 7 8 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 8 84 2 3 4 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 8 84 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 8 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 84 4 1 2 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 84 (Polychromatic418967fa.accept_15_3_8_9_1_795 3 8 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 84 2 1 4 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 84 (accept_3_4 1 8 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 84)))))))) (allB_succ 7 84 (allA_succ_of_accept 6 7 84
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 84 (accept_3_5 5 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 84
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 84 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 84 (accept_3_5 2 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 7 84 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 7 84))))))) (allB_succ 6 84 (allA_succ_of_accept 5 6 84
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 6 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 84 2 2 3 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 84 3 1 2 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 84 2 1 3 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 84 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 6 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 6 84)))))) (allB_succ 5 84 (allA_succ_of_accept 4 5 84 (accept_3_4 4 5 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 84 (Polychromatic418967fa.accept_13_3_5_6_1_3192 3 5 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 84
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 5 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 84 (accept_3_4 1 5 84 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 84))))) (allB_succ
  4 84 (allA_succ_of_accept 3 4 84 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 4 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 84 2 1 2 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 84 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 4 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 84)))) (allB_succ 3 84 (allA_succ_of_accept 2 3 84
  (Polychromatic418967fa.accept_18_2_3_12_1_1155 2 3 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 84 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 3 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 84))) (allB_succ 2 84 (allA_succ_of_accept 1 2 84 (accept_3_4 1 2 84
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 84)) (allB_two
  84))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


