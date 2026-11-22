-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch101
-- name    : Polychromatic418967fa_Branch101
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:10:01.121601+00:00
-- url     : https://prove2.me/theorems/f3c1a15f-41d2-4f15-9e02-0719ba825d4a
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

def Polychromatic418967fa.branch_101 : allB 101 101 :=
  allB_succ' 2 100 101 (Eq.refl Bool.true) (allA_of_3_0 2 100 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  99 101 (Eq.refl Bool.true) (allA_succ_of_accept 2 99 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 101 (accept_3_2 1 99 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99 101))) (allB_succ' 4 98 101 (Eq.refl Bool.true) (allA_succ_of_accept 3 98
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 98 101 (Polychromatic418967fa.accept_19_2_3_6_1_4415 2 98 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 101 (accept_3_2 1 98 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 101)))) (allB_succ' 5 97 101 (Eq.refl Bool.true) (allA_of_3_0 5 97 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 96 101 (Eq.refl Bool.true) (allA_succ_of_accept 5 96 101
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 101 (accept_3_2 4 96 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  101 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 96 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 101 (accept_3_2 1 96 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96 101)))))) (allB_succ' 7 95 101 (Eq.refl Bool.true) (allA_succ_of_accept 6 95 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 101 (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 95 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 101 (accept_3_2 4 95 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 95 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 101 (accept_3_2 1 95 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 101))))))) (allB_succ' 8 94 101 (Eq.refl Bool.true) (allA_of_3_0
  8 94 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 93 101 (Eq.refl Bool.true) (allA_succ_of_accept 8 93
  101 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 101 (accept_3_2 7 93 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  101 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 93 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 101 (accept_3_2 4 93 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 101 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 93 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 101 (accept_3_2 1 93 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 101))))))))) (allB_succ' 10 92 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 92 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 101 (Polychromatic418967fa.accept_16_8_12_5_1_200 8 92 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 92 101 (accept_3_2 7 92 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92 101 (Polychromatic418967fa.accept_10_6_2_1_1_494 6
  92 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 92 101
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 92 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 92 101 (accept_3_2 4 92 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 92
  101 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 92 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 92 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 101 (accept_3_2 1 92 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 101)))))))))) (allB_succ' 11 91 101 (Eq.refl Bool.true) (allA_of_3_0 11 91 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 90 101 (Eq.refl Bool.true) (allA_succ_of_accept 11 90 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 101 (accept_3_2 10 90 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 90 101 (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 90 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 101 (accept_3_2 7 90 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 101 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 90 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 101
  (Polychromatic418967fa.accept_19_5_14_6_1_4413 5 90 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 101 (accept_3_2 4 90 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 90 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 101 (accept_3_2 1 90 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 90 101)))))))))))) (allB_succ' 13 89 101 (Eq.refl Bool.true) (allA_succ_of_accept 12 89 101
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 89 101 (Polychromatic418967fa.accept_16_11_9_5_1_4412 11 89 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 101 (accept_3_2 10 89 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 89 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 89 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 101 (Polychromatic418967fa.accept_7_1_5_3_1_268 8
  89 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 101 (accept_3_2 7 89 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  89 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 101
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 101 (accept_3_2 4 89 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  101 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 89 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 89 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 101 (accept_3_2 1 89 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 101))))))))))))) (allB_succ' 14 88 101 (Eq.refl Bool.true) (allA_of_3_0 14 88 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 87 101 (Eq.refl Bool.true) (allA_succ_of_accept 14 87 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 101 (accept_3_2 13 87 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 101 (Polychromatic418967fa.accept_16_11_7_5_1_4364 11 87 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 101 (accept_3_2 10 87 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 101 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 87 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 101 (accept_3_2 7 87 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 101 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 87 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 101 (accept_3_2 4 87 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 101 (accept_3_2 1 87 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 101))))))))))))))) (allB_succ' 16 86 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 86 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 101 (Polychromatic418967fa.accept_19_14_10_6_1_4372 14 86
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 86 101 (accept_3_2 13 86 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 86 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 12
  86 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 86 101 (accept_3_2 10 86 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  86 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 86 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 86 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 86 101 (accept_3_2 7 86 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 86 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 86 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 86 101
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 86 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 86 101 (accept_3_2 4 86 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 86
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 86 101 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 86 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 101 (accept_3_2 1 86 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 101)))))))))))))))) (allB_succ' 17 85 101 (Eq.refl Bool.true) (allA_of_3_0 17 85 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 84 101 (Eq.refl Bool.true) (allA_succ_of_accept 17 84 101
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 101 (accept_3_2 16 84 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 101 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 84 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 101 (accept_3_2 13 84 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 101 (Polychromatic418967fa.accept_13_12_6_10_1_667 12 84 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 101
  (Polychromatic418967fa.accept_20_11_4_1_1_4389 11 84 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 101 (accept_3_2 10 84 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 101 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 101 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 84 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 101 (accept_3_2 7 84 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 84 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 101
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 101 (accept_3_2 4 84 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  101 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 84 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 84 101 (Polychromatic418967fa.accept_13_2_6_10_1_2703 2 84 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 101 (accept_3_2 1 84 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84 101)))))))))))))))))) (allB_succ' 19 83 101 (Eq.refl Bool.true) (allA_succ_of_accept
  18 83 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 101 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 83 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 101 (accept_3_2 16 83 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 101 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 83 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 101 (accept_3_2 13 83 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 101 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 83 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 101 (accept_3_2 10 83 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 83 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 101
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 83 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 101 (accept_3_2 7 83 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 101 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 83 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 101 (accept_3_2 4 83 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 101 (Polychromatic418967fa.accept_15_3_8_11_1_4386 3 83 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 101 (accept_3_2 1 83 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83 101))))))))))))))))))) (allB_succ' 20 82 101 (Eq.refl Bool.true)
  (allA_of_3_0 20 82 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 81 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 20 81 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 101 (accept_3_2 19 81 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 101 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 81 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 101 (Polychromatic418967fa.accept_11_6_4_2_1_599
  17 81 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 101 (accept_3_2 16
  81 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 101
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 101 (accept_3_2 13 81 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 101 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 81 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 101
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 81 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 101 (accept_3_2 10 81 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 101 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 81 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 101 (accept_3_2 7 81 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 101
  (Polychromatic418967fa.accept_15_5_6_11_1_854 5 81 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 101 (accept_3_2 4 81 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  101 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 101 (accept_3_2 1 81 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 101))))))))))))))))))))) (allB_succ' 22 80 101 (Eq.refl Bool.true) (allA_succ_of_accept 21 80
  101 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 80 101 (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 80 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 80 101 (accept_3_2 19 80 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 80 101 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 80 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 101 (Polychromatic418967fa.accept_15_2_5_11_1_1563
  17 80 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 101 (accept_3_2 16
  80 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 101
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 80 101 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 80 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 101 (accept_3_2 13 80 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 80 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 80 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 101
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 80 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 80 101 (accept_3_2 10 80 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  80 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 80 101 (Polychromatic418967fa.accept_13_8_2_10_1_652 8 80 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 101 (accept_3_2 7 80 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 80 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 80 101
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 80 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 80 101 (accept_3_2 4 80 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80
  101 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 80 101 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 80 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 101 (accept_3_2 1 80 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 101)))))))))))))))))))))) (allB_succ' 23 79 101 (Eq.refl Bool.true) (allA_of_3_0 23 79 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 78 101 (Eq.refl Bool.true) (allA_succ_of_accept 23 78 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 101 (accept_3_2 22 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 101 (Polychromatic418967fa.accept_19_1_2_6_1_4411 20 78 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 101 (accept_3_2 19 78 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 101 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 78 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 101
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 101 (accept_3_2 16 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 101 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 78 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 101 (accept_3_2 13 78 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 78 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 101 (accept_3_2 10 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 101 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 78 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 101 (accept_3_2 7 78 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 101 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 78 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 101
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 101 (accept_3_2 4 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 78 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 101 (accept_3_2 1 78 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 101)))))))))))))))))))))))) (allB_succ' 25 77 101 (Eq.refl Bool.true) (allA_succ_of_accept 24
  77 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 101 (Polychromatic418967fa.accept_17_6_9_16_1_4410 23 77 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 101 (accept_3_2 22 77 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 77 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 101
  (Polychromatic418967fa.accept_13_7_12_10_1_640 20 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 101 (accept_3_2 19 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 101 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 101 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 101 (accept_3_2 16 77 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 77 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 101
  (Polychromatic418967fa.accept_10_4_7_1_1_471 14 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 101 (accept_3_2 13 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 101 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 77 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 101 (accept_3_2 10 77 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 101 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 77 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 101
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 101 (accept_3_2 7 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  101 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 101 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 77 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 101 (accept_3_2 4 77 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 77 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 101 (Polychromatic418967fa.accept_13_2_12_10_1_2649
  2 77 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 101 (accept_3_2 1 77
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 101))))))))))))))))))))))))) (allB_succ' 26 76 101 (Eq.refl
  Bool.true) (allA_of_3_0 26 76 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 75 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 75 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 101 (accept_3_2 25 75 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  75 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 101 (accept_3_2 22 75
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 101
  (Polychromatic418967fa.accept_12_9_3_5_1_423 21 75 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 101 (accept_3_2 19 75 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 101 (Polychromatic418967fa.accept_9_8_3_2_1_417 17
  75 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 101 (accept_3_2 16 75
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 101
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 101 (accept_3_2 13 75 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 101 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 75 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 101
  (Polychromatic418967fa.accept_19_11_18_6_1_3113 11 75 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 101 (accept_3_2 10 75 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  75 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 101 (accept_3_2 7 75 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 101
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 75 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 101 (accept_3_2 4 75 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  101 (Polychromatic418967fa.accept_17_3_7_16_1_3251 3 75 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 75 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 101 (accept_3_2 1 75 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 75 101))))))))))))))))))))))))))) (allB_succ' 28 74 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 74 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 101 (Polychromatic418967fa.accept_17_9_6_16_1_3280 26 74
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 101 (accept_3_2 25 74 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 101 (Polychromatic418967fa.accept_17_7_6_16_1_2195
  24 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 74 101 (accept_3_2 22 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  74 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 74 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 74 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 101 (accept_3_2 19 74 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 101 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 74 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 101
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 74 101 (accept_3_2 16 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  74 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 74 101 (Polychromatic418967fa.accept_13_1_9_10_1_625 14 74 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 101 (accept_3_2 13 74 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 101 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 74 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 74 101 (accept_3_2 10 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  74 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 74 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 74 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 101 (accept_3_2 7 74 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 74 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 101
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 101 (accept_3_2 4 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 101 (Polychromatic418967fa.accept_21_2_11_17_1_4395 2 74 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 101 (accept_3_2 1 74 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 101)))))))))))))))))))))))))))) (allB_succ' 29 73 101 (Eq.refl Bool.true) (allA_of_3_0 29 73
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 72 101 (Eq.refl Bool.true) (allA_succ_of_accept 29 72 101
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 101 (accept_3_2 28 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 72 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 101 (accept_3_2 25 72 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 101 (Polychromatic418967fa.accept_19_5_15_6_1_1986 24 72 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 101
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 101 (accept_3_2 22 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 101 (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 72 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 101 (accept_3_2 19 72 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 101 (Polychromatic418967fa.accept_21_18_9_17_1_4409 18 72 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 101
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 101 (accept_3_2 16 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 101 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 72 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 101 (accept_3_2 13 72 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 72 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 101
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 11 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 101 (accept_3_2 10 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 101 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 72 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 101 (accept_3_2 7 72 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 72 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 101
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 101 (accept_3_2 4 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  101 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 72 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 101 (Polychromatic418967fa.accept_19_2_15_6_1_4408 2 72 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 101 (accept_3_2 1 72 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 101)))))))))))))))))))))))))))))) (allB_succ' 31 71 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 30 71 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 101 (Polychromatic418967fa.accept_13_3_6_10_1_2658 29 71
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 101 (accept_3_2 28 71 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 101 (Polychromatic418967fa.accept_16_11_7_5_1_4364
  27 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 101 (accept_3_2 25 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 101 (accept_3_2 22 71 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 71 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 101
  (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 101 (accept_3_2 19 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 101 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 71 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 101 (accept_3_2 16 71 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 71 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 101 (accept_3_2 13 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 101 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 101 (accept_3_2 10 71 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 71 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 101
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 101 (accept_3_2 7 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 101 (accept_3_2 4 71 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 71 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 101 (accept_3_2 1 71 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 101))))))))))))))))))))))))))))))) (allB_succ' 32 70 101
  (Eq.refl Bool.true) (allA_of_3_0 32 70 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 69 101 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 69 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 101 (accept_3_2 31 69 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 101
  (Polychromatic418967fa.accept_17_12_1_16_1_4360 29 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 101 (accept_3_2 28 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 101 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 101 (accept_3_2 25 69 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 101 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 69 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 101
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 101 (accept_3_2 22 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 101 (accept_3_2 19 69 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 101
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 101 (accept_3_2 16 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 101 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 101 (accept_3_2 13 69 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 101
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 101 (accept_3_2 10 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 101 (accept_3_2 7 69 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 101 (Polychromatic418967fa.accept_13_6_4_10_1_660 6 69 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 101
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 101 (accept_3_2 4 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  101 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 69 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 101 (accept_3_2 1 69 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 101))))))))))))))))))))))))))))))))) (allB_succ' 34 68 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 68 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 101 (Polychromatic418967fa.accept_13_6_3_10_1_698 32 68 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 101 (accept_3_2 31 68 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 30
  68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 101
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 68 101 (accept_3_2 28 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  68 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 68 101 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 68 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 101 (accept_3_2 25 68 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 68 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 101
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 68 101 (accept_3_2 22 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  68 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 68 101 (Polychromatic418967fa.accept_13_7_3_10_1_656 20 68 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 101 (accept_3_2 19 68 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 101 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 68 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 101
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 68 101 (accept_3_2 16 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  68 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 68 101 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 68 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 101 (accept_3_2 13 68 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 68 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 101
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 68 101 (accept_3_2 10 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  68 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 68 101 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 68 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 101 (accept_3_2 7 68 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 68 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 101
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 5 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 101 (accept_3_2 4 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  101 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 68 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 101 (accept_3_2 1 68 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 101)))))))))))))))))))))))))))))))))) (allB_succ' 35 67 101 (Eq.refl Bool.true) (allA_of_3_0
  35 67 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 66 101 (Eq.refl Bool.true) (allA_succ_of_accept 35
  66 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 66 101 (accept_3_2 34 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 66 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 66 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 101 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 66 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 101 (accept_3_2 31 66 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 101 (Polychromatic418967fa.accept_13_4_1_10_1_693
  30 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 101
  (Polychromatic418967fa.accept_16_13_2_5_1_3336 29 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 101 (accept_3_2 28 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 101 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 66 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 101 (accept_3_2 25 66 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 66 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 101 (accept_3_2 22 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 101 (Polychromatic418967fa.accept_14_7_10_3_1_1034 21 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 101 (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 66 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 101 (accept_3_2 19 66 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 101 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 66 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 101
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 101 (accept_3_2 16 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 101 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 66 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 101 (accept_3_2 13 66 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 101 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 66 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 101 (accept_3_2 10 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 101 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 101 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 66 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 101 (accept_3_2 7 66 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 66 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 101
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 101 (accept_3_2 4 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 101 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 66 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 101 (accept_3_2 1 66 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 101)))))))))))))))))))))))))))))))))))) (allB_succ' 37 65 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 65 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 65 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 101 (Polychromatic418967fa.accept_19_16_8_6_1_4407 35 65
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 101 (accept_3_2 34 65 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 101
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 101 (accept_3_2 31 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 101 (Polychromatic418967fa.accept_20_10_5_1_1_4406 30 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 101 (accept_3_2 28 65 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 65 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 101
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 101 (accept_3_2 25 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 101 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 101 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 65 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 101 (accept_3_2 22 65 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 101 (Polychromatic418967fa.accept_15_6_5_11_1_2378 21 65 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 101
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 101 (accept_3_2 19 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 101 (Polychromatic418967fa.accept_27_18_11_20_1_4405 18 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 101 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 65 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 101 (accept_3_2 16 65 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 65 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 101
  (Polychromatic418967fa.accept_10_4_5_1_1_497 14 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 101 (accept_3_2 13 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 101 (Polychromatic418967fa.accept_17_11_14_16_1_1270 11 65 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 101 (accept_3_2 10 65 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 101 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 101
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 101 (accept_3_2 7 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  101 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 65 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 101 (accept_3_2 4 65 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 101 (Polychromatic418967fa.accept_19_3_8_6_1_4368 3 65 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 101 (Polychromatic418967fa.accept_15_2_5_11_1_1563
  2 65 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 101 (accept_3_2 1 65
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 101))))))))))))))))))))))))))))))))))))) (allB_succ' 38 64
  101 (Eq.refl Bool.true) (allA_of_3_0 38 64 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 63 101 (Eq.refl
  Bool.true) (allA_succ_of_accept 38 63 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 101 (accept_3_2 37 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 101 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 63 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 101
  (Polychromatic418967fa.accept_17_1_12_16_1_2211 35 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 101 (accept_3_2 34 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  63 101 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 63 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 101 (accept_3_2 31 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 101
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 29 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 101 (accept_3_2 28 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  63 101 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 63 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 101 (accept_3_2 25 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 101 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 63 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 101
  (Polychromatic418967fa.accept_15_8_3_11_1_849 23 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 101 (accept_3_2 22 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  63 101 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 63 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 101 (accept_3_2 19 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 101
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 101 (accept_3_2 16 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  63 101 (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 63 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 101 (accept_3_2 13 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 101 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 63 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 101
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 101 (accept_3_2 10 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  63 101 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 63 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 101 (accept_3_2 7 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 101
  (Polychromatic418967fa.accept_11_5_8_2_1_588 5 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 101 (accept_3_2 4 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63
  101 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 63 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 63 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 101 (accept_3_2 1 63 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 63 101))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 62 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 101 (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 62
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 101 (accept_3_2 37 62 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 101 (Polychromatic418967fa.accept_10_6_2_1_1_494
  36 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 101 (accept_3_2 34 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 62 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 101 (accept_3_2 31 62 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 62 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 101
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 101 (accept_3_2 28 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 101 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 62 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 101 (accept_3_2 25 62 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 62 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 101 (accept_3_2 22 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 101 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 62 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 101 (accept_3_2 19 62 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 62 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 101
  (Polychromatic418967fa.accept_22_17_18_13_1_4404 17 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 62 101 (accept_3_2 16 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 62 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 101 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 62 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 101 (accept_3_2 13 62 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 12
  62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 101 (accept_3_2 10 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 101 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 62 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 101 (accept_3_2 7 62 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 62 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 101
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 101 (accept_3_2 4 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 62 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 101 (accept_3_2 1 62 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 101)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 61 101 (Eq.refl Bool.true)
  (allA_of_3_0 41 61 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 60 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 60 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 101 (accept_3_2 40 60 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 101
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 38 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 60 101 (accept_3_2 37 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  60 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 60 101 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 60 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 101 (accept_3_2 34 60 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 101 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 60 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 101
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 101 (accept_3_2 31 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  60 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 60 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 101 (accept_3_2 28 60 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 101
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 60 101 (accept_3_2 25 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  60 101 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 60 101 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 101 (accept_3_2 22 60 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 101
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 60 101 (accept_3_2 19 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  60 101 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 60 101 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 101 (accept_3_2 16 60 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 60 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 101
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 60 101 (accept_3_2 13 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  60 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 60 101 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 60 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 101 (accept_3_2 10 60 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 60 101 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 60 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 101
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 101 (accept_3_2 7 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60
  101 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 101 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 60 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 101 (accept_3_2 4 60 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 60 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 60 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 101 (Polychromatic418967fa.accept_13_2_8_10_1_1902
  2 60 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 101 (accept_3_2 1 60
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 101)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43
  59 101 (Eq.refl Bool.true) (allA_succ_of_accept 42 59 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 101
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 41 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 101 (accept_3_2 40 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 101 (accept_3_2 37 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 101 (Polychromatic418967fa.accept_17_2_8_16_1_4403 36 59 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 101
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 101 (accept_3_2 34 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 101 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 101 (accept_3_2 31 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 101
  (Polychromatic418967fa.accept_13_3_7_10_1_668 29 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 101 (accept_3_2 28 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 101 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 101 (accept_3_2 25 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 101
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 23 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 101 (accept_3_2 22 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 101 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 101 (accept_3_2 19 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 101
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 101 (accept_3_2 16 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 101 (accept_3_2 13 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 59 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 101
  (Polychromatic418967fa.accept_23_11_13_9_1_4401 11 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 101 (accept_3_2 10 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 101 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 101 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 101 (accept_3_2 7 59 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 101
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 101 (accept_3_2 4 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  101 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 59 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 101 (accept_3_2 1 59 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 101))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 58 101 (Eq.refl Bool.true)
  (allA_of_3_0 44 58 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 57 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 57 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 101 (accept_3_2 43 57 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 57 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 101 (Polychromatic418967fa.accept_9_5_3_2_1_171 41
  57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 101 (accept_3_2 40 57
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 101
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 101 (accept_3_2 37 57 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 101 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 101 (Polychromatic418967fa.accept_9_8_3_2_1_417 35
  57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 101 (accept_3_2 34 57
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 101
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 101 (accept_3_2 31 57 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 101
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 101 (accept_3_2 28 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 57 101 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 57 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 101 (accept_3_2 25 57 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 24
  57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 101
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 101 (accept_3_2 22 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  57 101 (Polychromatic418967fa.accept_13_8_5_10_1_2701 21 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 57 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 101 (accept_3_2 19 57 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 101 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 101
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 101 (accept_3_2 16 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  57 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 57 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 101 (accept_3_2 13 57 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 101
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 101 (accept_3_2 10 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  57 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 57 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 101 (accept_3_2 7 57 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 57 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 101
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 101 (accept_3_2 4 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57
  101 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 57 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 101 (accept_3_2 1 57 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 57 101))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 56 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 101 (Polychromatic418967fa.accept_13_5_4_10_1_1244 44 56
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 56 101 (accept_3_2 43 56 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 56 101 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  42 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 56 101
  (Polychromatic418967fa.accept_19_3_18_6_1_3112 41 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 56 101 (accept_3_2 40 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  56 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 56 101 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 56 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 101 (accept_3_2 37 56 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 101 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 56 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 56 101
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 56 101 (accept_3_2 34 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  56 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 56 101 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 56 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 101 (accept_3_2 31 56 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 56 101 (Polychromatic418967fa.accept_19_11_18_6_1_3113 30 56 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 101
  (Polychromatic418967fa.accept_16_13_8_5_1_3298 29 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 56 101 (accept_3_2 28 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  56 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 56 101 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 56 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 101 (accept_3_2 25 56 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 56 101 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 56 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 101
  (Polychromatic418967fa.accept_21_2_14_17_1_1689 23 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 56 101 (accept_3_2 22 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  56 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 56 101 (Polychromatic418967fa.accept_13_7_4_10_1_2675 20 56 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 101 (accept_3_2 19 56 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 101 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 56
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 101
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 56 101 (accept_3_2 16 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  56 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 56 101 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 56 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 101 (accept_3_2 13 56 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 101 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 56 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 101
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 56 101 (accept_3_2 10 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  56 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 56 101 (Polychromatic418967fa.accept_13_8_4_10_1_4358 8 56 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 56 101 (accept_3_2 7 56 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 56 101 (Polychromatic418967fa.accept_13_6_4_10_1_660 6 56 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 101
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 56 101 (accept_3_2 4 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56
  101 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 56 101 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 56 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 101 (accept_3_2 1 56 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 101)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 55 101 (Eq.refl Bool.true)
  (allA_of_3_0 47 55 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 54 101 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 101 (accept_3_2 46 54 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 101 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 44
  54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 101 (accept_3_2 43 54
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 101
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 101 (Polychromatic418967fa.accept_17_7_3_16_1_2208 41 54 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 101 (accept_3_2 40 54 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 101
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 38 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 101 (accept_3_2 37 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  54 101 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 54 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 101 (accept_3_2 34 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 101 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 54 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 101
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 32 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 101 (accept_3_2 31 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  54 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 54 101 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 101 (accept_3_2 28 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 101
  (Polychromatic418967fa.accept_19_7_16_6_1_4400 26 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 101 (accept_3_2 25 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 101 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 101 (accept_3_2 22 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 101 (Polychromatic418967fa.accept_13_8_2_10_1_652 21 54 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 101
  (Polychromatic418967fa.accept_15_5_9_11_1_4398 20 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 101 (accept_3_2 19 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 101 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 101 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 101 (accept_3_2 16 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 101
  (Polychromatic418967fa.accept_23_14_8_9_1_4397 14 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 101 (accept_3_2 13 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 101 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 101 (accept_3_2 10 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 101
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 101 (accept_3_2 7 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  101 (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 54 101 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 101 (accept_3_2 4 54 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 101
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 101 (accept_3_2 1 54 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  101)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 53 101 (Eq.refl Bool.true) (allA_succ_of_accept 48
  53 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 53 101 (Polychromatic418967fa.accept_19_9_15_6_1_4396 47 53 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 101 (accept_3_2 46 53 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 101 (Polychromatic418967fa.accept_22_1_9_13_1_2894 45 53
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 101
  (Polychromatic418967fa.accept_21_2_11_17_1_4395 44 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 101 (accept_3_2 43 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 101 (accept_3_2 40 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 53 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 101
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 101 (accept_3_2 37 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 101 (Polychromatic418967fa.accept_13_9_1_10_1_647 35 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 101 (accept_3_2 34 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 53 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 101
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 101 (accept_3_2 31 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 101 (accept_3_2 28 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 53 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 101
  (Polychromatic418967fa.accept_11_4_9_2_1_259 26 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 101 (accept_3_2 25 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 101 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 101 (accept_3_2 22 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 53 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 101
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 101 (accept_3_2 19 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 101 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 101 (Polychromatic418967fa.accept_13_4_1_10_1_693 17 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 101 (accept_3_2 16 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 53 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 101
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 101 (accept_3_2 13 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 101 (Polychromatic418967fa.accept_13_11_1_10_1_648 11 53 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 101 (accept_3_2 10 53 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 101 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 53 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 101
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 101 (accept_3_2 7 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  101 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 101 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 53 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 101 (accept_3_2 4 53 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 53 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 101 (Polychromatic418967fa.accept_10_2_3_1_1_481 2
  53 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 101 (accept_3_2 1 53 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 101))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  50 52 101 (Eq.refl Bool.true) (allA_of_3_0 50 52 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 101
  (allA_succ_of_accept 50 51 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 101 (accept_3_2 49 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 101 (accept_3_2 46 51
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 101
  (Polychromatic418967fa.accept_12_9_3_5_1_423 45 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 101 (accept_3_2 43 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 41
  51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 101 (accept_3_2 40 51
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 101
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 101 (accept_3_2 37 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 101 (Polychromatic418967fa.accept_9_8_6_2_1_744 35
  51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 101 (accept_3_2 34 51
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 101
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 101 (accept_3_2 31 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 101 (accept_3_2 28 51
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 101
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 101 (accept_3_2 25 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 101 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 51 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 101
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 101 (accept_3_2 22 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  51 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 51 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 101 (accept_3_2 19 51 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 101
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 101 (accept_3_2 16 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  51 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 51 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 101 (accept_3_2 13 51 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 101
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 101 (accept_3_2 10 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 51 101 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 101 (accept_3_2 7 51 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 101
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 101 (accept_3_2 4 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  101 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 51 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 101 (accept_3_2 1 51 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 101))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 101 (allA_succ_of_accept
  49 50 101 (accept_3_2 49 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 101
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 101 (accept_3_2 46 50 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 50 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 101 (accept_3_2 43 50
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 101
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 101 (Polychromatic418967fa.accept_13_2_11_10_1_1881 41 50 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 101 (accept_3_2 40 50 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 101
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 38 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 50 101 (accept_3_2 37 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 50 101 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 50 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 50 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 101 (accept_3_2 34 50 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 101
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 101 (accept_3_2 31 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 101 (Polychromatic418967fa.accept_13_3_11_10_1_2647 29 50 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 101 (accept_3_2 28 50 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 101
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 101 (accept_3_2 25 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 101 (accept_3_2 22 50 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 101
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 101 (accept_3_2 19 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 101 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 101 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 50 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 101 (accept_3_2 16 50 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 101
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 101 (accept_3_2 13 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 101 (accept_3_2 10 50 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 101
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 101 (accept_3_2 7 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  101 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 50 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 101 (accept_3_2 4 50 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  50 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 101 (accept_3_2 1 50 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 101)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 101 (allA_of_3_0 49 49 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 101 (allA_succ_of_accept 47 48
  101 (Polychromatic418967fa.accept_19_9_10_6_1_4394 47 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 48 101 (accept_3_2 46 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 101 (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 48 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 48 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 101 (accept_3_2 43 48 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 42
  48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 101
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 101 (accept_3_2 40 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 101 (Polychromatic418967fa.accept_13_12_9_10_1_1223 38 48 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 101 (accept_3_2 37 48 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 101 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 48 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 101
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 101 (accept_3_2 34 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 48 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 101 (accept_3_2 31 48 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 48 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 101
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 101 (accept_3_2 28 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 101 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 101 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 48 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 101 (accept_3_2 25 48 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 48 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 101
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 101 (accept_3_2 22 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 101 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 101 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 48 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 101 (accept_3_2 19 48 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 48 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 101
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 101 (accept_3_2 16 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 101 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 48 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 101 (accept_3_2 13 48 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 101 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 48 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 101
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 101 (accept_3_2 10 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 101 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 48 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 101 (accept_3_2 7 48 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 48 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 101
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 101 (accept_3_2 4 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  101 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 48 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 48 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 101 (accept_3_2 1 48 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 101)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 101 (allA_succ_of_accept 46
  47 101 (accept_3_2 46 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 101
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 101 (accept_3_2 43 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 101 (Polychromatic418967fa.accept_13_2_8_10_1_1902
  41 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 101 (accept_3_2 40
  47 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 101
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 39 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 101 (accept_3_2 37 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 101 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 101 (Polychromatic418967fa.accept_15_5_2_11_1_1596
  35 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 101 (accept_3_2 34
  47 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 101
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 101 (Polychromatic418967fa.accept_19_13_9_6_1_4393 32 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 101 (accept_3_2 31 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 101 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 101 (accept_3_2 28 47
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 101
  (Polychromatic418967fa.accept_31_27_16_8_1_4392 27 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 101 (accept_3_2 25 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 101 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 47 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 101 (accept_3_2 22 47
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 101
  (Polychromatic418967fa.accept_15_6_2_11_1_325 21 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 101 (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 101 (accept_3_2 19 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 101 (Polychromatic418967fa.accept_13_4_8_10_1_671
  17 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 101 (accept_3_2 16
  47 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 101
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 101 (accept_3_2 13 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 101 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 47 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 101 (Polychromatic418967fa.accept_13_11_8_10_1_676
  11 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 101 (accept_3_2 10
  47 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 101
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 101 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 101 (accept_3_2 7 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 101 (Polychromatic418967fa.accept_13_5_8_10_1_4363
  5 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 101 (accept_3_2 4 47
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 101
  (Polychromatic418967fa.accept_17_3_13_16_1_2183 3 47 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 101 (accept_3_2 1 47 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 101))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 101 (allA_of_3_0 46 46 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 101 (allA_succ_of_accept 44 45 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 101 (accept_3_2 43 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 101 (Polychromatic418967fa.accept_13_3_6_10_1_2658 42 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 101 (Polychromatic418967fa.accept_13_2_6_10_1_2703 41 45 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 101 (accept_3_2 40 45 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 101 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 45 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 101 (accept_3_2 37 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 101 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 101 (Polychromatic418967fa.accept_13_9_6_10_1_666 35 45 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 101 (accept_3_2 34 45 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 101 (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 45 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 101 (accept_3_2 31 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 101 (Polychromatic418967fa.accept_13_4_6_10_1_1199 30 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 101 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 45 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 101 (accept_3_2 28 45 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 101 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 45 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 101 (accept_3_2 25 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 101 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 101 (Polychromatic418967fa.accept_20_3_5_1_1_4391 23 45 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 101 (accept_3_2 22 45 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 101 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 45 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 101 (accept_3_2 19 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 101 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 101 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 45 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 101 (accept_3_2 16 45 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 101 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 45 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 101 (accept_3_2 13 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 101 (Polychromatic418967fa.accept_13_12_6_10_1_667 12 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 101 (Polychromatic418967fa.accept_27_11_18_20_1_4390 11 45 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 101 (accept_3_2 10 45 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 101 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 45 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 101 (accept_3_2 7 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  101 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 45 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 101 (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 45 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 101 (accept_3_2 4 45 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 101 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 45 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 101 (accept_3_2 1 45 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 101))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  101 (allA_succ_of_accept 43 44 101 (accept_3_2 43 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 101 (accept_3_2 40 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 101
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 101 (accept_3_2 37 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 101 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 101 (accept_3_2 34 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 101
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 101 (accept_3_2 31 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 101 (accept_3_2 28 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 101
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 101 (accept_3_2 25 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 101 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 101 (accept_3_2 22 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 101
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 101 (accept_3_2 19 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 101 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 101 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 101 (accept_3_2 16 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 101
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 101 (accept_3_2 13 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 101 (Polychromatic418967fa.accept_20_11_4_1_1_4389 11 44 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 101 (accept_3_2 10 44 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 101
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 101 (accept_3_2 7 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  101 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 44 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 101 (accept_3_2 4 44 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 101 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  44 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 101 (accept_3_2 1 44 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 101)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  101 (allA_of_3_0 43 43 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 101 (allA_succ_of_accept 41 42 101
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 101 (accept_3_2 40 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 101 (Polychromatic418967fa.accept_15_8_12_11_1_1570 38 42 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 101 (accept_3_2 37 42 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 101 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 101 (accept_3_2 34 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 101 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 101 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 42 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 101 (accept_3_2 31 42 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 42 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 101
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 101 (accept_3_2 28 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 101 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 42 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 101 (accept_3_2 25 42 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 101 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 42 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 101 (accept_3_2 22 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 101 (Polychromatic418967fa.accept_13_7_3_10_1_656 20 42 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 101 (accept_3_2 19 42 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 101 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 42 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 101
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 101 (accept_3_2 16 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 101 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 42 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 101 (accept_3_2 13 42 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 42 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 101 (accept_3_2 10 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 101 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 101 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 42 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 101 (accept_3_2 7 42 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 101 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 101
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 101 (accept_3_2 4 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 101 (Polychromatic418967fa.accept_13_2_3_10_1_658 2 42 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 101 (accept_3_2 1 42 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 101)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 101 (allA_succ_of_accept 40 41
  101 (accept_3_2 40 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 101
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 101 (Polychromatic418967fa.accept_11_5_8_2_1_588 38 41 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 101 (accept_3_2 37 41 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 101 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 41 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 101 (Polychromatic418967fa.accept_9_8_5_2_1_422 35
  41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 101 (accept_3_2 34 41
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 101
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 41 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 101 (accept_3_2 31 41 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 41 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 101 (Polychromatic418967fa.accept_13_3_2_10_1_2697
  29 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 101 (accept_3_2 28
  41 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 101
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 41 101 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 41 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 101 (accept_3_2 25 41 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 41 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 41 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 101 (accept_3_2 22 41
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 101 (Polychromatic418967fa.accept_9_3_5_2_1_28
  21 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 101
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 101 (accept_3_2 19 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 101 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 41 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 101 (accept_3_2 16 41 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 41 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 101
  (Polychromatic418967fa.accept_16_14_9_5_1_4388 14 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 101 (accept_3_2 13 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 101 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 101 (accept_3_2 10 41 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 101
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 101 (accept_3_2 7 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  101 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 101 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 41 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 101 (accept_3_2 4 41 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 41 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  41 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 101 (accept_3_2 1 41 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 101))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 101
  (allA_of_3_0 40 40 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 101 (allA_succ_of_accept 38 39 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 101 (accept_3_2 37 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 101 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 39 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 101 (accept_3_2 34 39 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 39 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 101 (accept_3_2 31 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 39 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 101 (accept_3_2 28 39 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 101 (accept_3_2 25 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 101 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 39 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 101 (accept_3_2 22 39 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 101 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 39 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 101 (accept_3_2 19 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 101 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 39 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 101 (accept_3_2 16 39 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 101 (accept_3_2 13 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 101 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 101 (Polychromatic418967fa.accept_16_11_7_5_1_4364 11 39 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 101 (accept_3_2 10 39 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 101 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 39 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 101 (accept_3_2 7 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 101 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 39 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 101 (accept_3_2 4 39 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 101 (Polychromatic418967fa.accept_19_3_1_6_1_3114 3 39 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 101 (accept_3_2 1 39 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 101))))))))))))))))))))))))))))))))))))))) (allB_succ 38 101
  (allA_succ_of_accept 37 38 101 (accept_3_2 37 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 101 (Polychromatic418967fa.accept_16_4_6_5_1_2245 36 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 101 (accept_3_2 34 38 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 101
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 101 (accept_3_2 31 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 101 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 101 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 38 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 101 (accept_3_2 28 38 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 101
  (Polychromatic418967fa.accept_27_26_11_20_1_4387 26 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 38 101 (accept_3_2 25 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 38 101 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 38 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 38 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 101 (accept_3_2 22 38 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 101
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 101 (accept_3_2 19 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 101 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 101 (Polychromatic418967fa.accept_16_1_6_5_1_4385 17 38 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 101 (accept_3_2 16 38 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 101
  (Polychromatic418967fa.accept_18_14_2_11_1_4384 14 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 101 (accept_3_2 13 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 101 (Polychromatic418967fa.accept_15_12_8_11_1_4383 12 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 101 (accept_3_2 10 38 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 101
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 101 (accept_3_2 7 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  101 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 38 101 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 38 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 101 (accept_3_2 4 38 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 38 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 101
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 2 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 38 101 (accept_3_2 1 38 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  101)))))))))))))))))))))))))))))))))))))) (allB_succ 37 101 (allA_of_3_0 37 37 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 36 101 (allA_succ_of_accept 35 36 101 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 36 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 101 (accept_3_2 34 36 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 101
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 101 (accept_3_2 31 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  36 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 36 101 (Polychromatic418967fa.accept_21_8_15_17_1_4382 29 36 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 101 (accept_3_2 28 36 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 101 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 36 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 101
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 101 (accept_3_2 25 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  36 101 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 36 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 101 (accept_3_2 22 36 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 101 (Polychromatic418967fa.accept_22_21_14_13_1_4381 21 36 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 101
  (Polychromatic418967fa.accept_15_5_6_11_1_854 20 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 101 (accept_3_2 19 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  36 101 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 36 101 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 36 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 101 (accept_3_2 16 36 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 101 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 36 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 101
  (Polychromatic418967fa.accept_17_14_2_16_1_4380 14 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 101 (accept_3_2 13 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  36 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 36 101 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 101 (accept_3_2 10 36 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 36 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 101
  (Polychromatic418967fa.accept_16_8_4_5_1_4379 8 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 101 (accept_3_2 7 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36
  101 (Polychromatic418967fa.accept_16_6_4_5_1_2272 6 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 36 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 101 (accept_3_2 4 36 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 101 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 36 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 101
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 36 101 (accept_3_2 1 36 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  101)))))))))))))))))))))))))))))))))))) (allB_succ 35 101 (allA_succ_of_accept 34 35 101 (accept_3_2 34 35 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 33
  35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 101
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 101 (accept_3_2 31 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 101 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 35 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 101 (accept_3_2 28 35 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 101 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 35 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 101 (accept_3_2 25 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 101 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 35 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 101 (accept_3_2 22 35 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 35 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 101
  (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 101 (accept_3_2 19 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 101 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 35 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 101 (accept_3_2 16 35 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 35 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 101 (accept_3_2 13 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 101 (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 35 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 101 (accept_3_2 10 35 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 101 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 101
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 101 (accept_3_2 7 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 101 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 35 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 101 (accept_3_2 4 35 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 35 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 101 (accept_3_2 1 35 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 101))))))))))))))))))))))))))))))))))) (allB_succ 34 101
  (allA_of_3_0 34 34 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 101 (allA_succ_of_accept 32 33 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 101 (accept_3_2 31 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 101 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 33 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 101 (accept_3_2 28 33 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 101 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 33 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 101 (accept_3_2 25 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 101 (Polychromatic418967fa.accept_18_6_15_11_1_3141 24 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 33 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 101 (accept_3_2 22 33 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 101 (accept_3_2 19 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 101 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 101 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 33 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 101 (accept_3_2 16 33 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 101 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 101 (accept_3_2 13 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 101 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 101 (Polychromatic418967fa.accept_19_11_14_6_1_4378 11 33 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 101 (accept_3_2 10 33 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 101 (accept_3_2 7 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  101 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 33 101 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 33 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 101 (accept_3_2 4 33 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 33 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 101 (accept_3_2 1 33 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33
  101))))))))))))))))))))))))))))))))) (allB_succ 32 101 (allA_succ_of_accept 31 32 101 (accept_3_2 31 32 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 32 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 101
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 32 101 (accept_3_2 28 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  32 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 32 101 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 32 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 101 (accept_3_2 25 32 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 32 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 101
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 32 101 (accept_3_2 22 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  32 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 32 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 32 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 101 (accept_3_2 19 32 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 101 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 32 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 101
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 101 (accept_3_2 16 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  32 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 32 101 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 32 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 101 (accept_3_2 13 32 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 32 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 101
  (Polychromatic418967fa.accept_17_11_15_16_1_4377 11 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 32 101 (accept_3_2 10 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 32 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 32 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 101 (accept_3_2 7 32 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  32 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 101
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 101 (accept_3_2 4 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  101 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 101 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 32 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 101 (accept_3_2 1 32 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 101)))))))))))))))))))))))))))))))) (allB_succ 31 101 (allA_of_3_0 31 31 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 101 (allA_succ_of_accept 29 30 101
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 101 (accept_3_2 28 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 30 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 101 (accept_3_2 25 30 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 30 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 101 (accept_3_2 22 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 101 (Polychromatic418967fa.accept_13_8_4_10_1_4358 21 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 30 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 101 (accept_3_2 19 30 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 101 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 30 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 101
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 101 (accept_3_2 16 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 101 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 30 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 101 (accept_3_2 13 30 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 30 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 101 (accept_3_2 10 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 101 (Polychromatic418967fa.accept_16_9_14_5_1_2239 9 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 30 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 101 (accept_3_2 7 30 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 30 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 101
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 101 (accept_3_2 4 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 101 (Polychromatic418967fa.accept_21_2_9_17_1_4376 2 30 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 101 (accept_3_2 1 30 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 101)))))))))))))))))))))))))))))) (allB_succ 29 101 (allA_succ_of_accept 28 29 101
  (accept_3_2 28 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 101
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 29 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 101 (accept_3_2 25 29 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 101 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 29 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 101
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 101 (accept_3_2 22 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 101 (Polychromatic418967fa.accept_19_2_10_6_1_4373 21 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 101 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 29 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 101 (accept_3_2 19 29 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 101 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 29 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 101
  (Polychromatic418967fa.accept_16_1_13_5_1_2280 17 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 101 (accept_3_2 16 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 101 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 101 (Polychromatic418967fa.accept_19_14_10_6_1_4372 14 29 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 101 (accept_3_2 13 29 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 101
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 101 (accept_3_2 10 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 101 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 29 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 101 (accept_3_2 7 29 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 101 (Polychromatic418967fa.accept_13_6_3_10_1_698 6 29 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 101
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 101 (accept_3_2 4 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  101 (Polychromatic418967fa.accept_15_3_14_11_1_1579 3 29 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 29 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 29 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 101 (accept_3_2 1 29 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 29 101))))))))))))))))))))))))))))) (allB_succ 28 101 (allA_of_3_0 28 28 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 27 101 (allA_succ_of_accept 26 27 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 101 (accept_3_2 25 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 101 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 27 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 101 (accept_3_2 22 27 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 101 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 101 (accept_3_2 19 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 101 (Polychromatic418967fa.accept_13_4_1_10_1_693 17 27 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 101 (accept_3_2 16 27 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 101 (Polychromatic418967fa.accept_18_15_9_11_1_4371 15 27 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 101 (accept_3_2 13 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 101 (Polychromatic418967fa.accept_18_12_9_11_1_4370 12 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 101 (accept_3_2 10 27 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 101 (accept_3_2 7 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 101 (Polychromatic418967fa.accept_23_5_4_9_1_4369 5 27 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 101 (accept_3_2 4 27 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 101 (Polychromatic418967fa.accept_19_3_8_6_1_4368 3 27 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 101 (accept_3_2 1 27 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 101))))))))))))))))))))))))))) (allB_succ 26 101
  (allA_succ_of_accept 25 26 101 (accept_3_2 25 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  26 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 101 (accept_3_2 22 26 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 101
  (Polychromatic418967fa.accept_11_9_4_2_1_600 20 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 101 (accept_3_2 19 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 101 (Polychromatic418967fa.accept_19_18_7_6_1_4367 18 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 101 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 26 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 101 (accept_3_2 16 26 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 101
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 101 (accept_3_2 13 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 101 (accept_3_2 10 26 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 101
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 101 (accept_3_2 7 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  101 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 26 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 101 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 101 (accept_3_2 4 26 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 26
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 101 (accept_3_2 1 26 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 101)))))))))))))))))))))))))) (allB_succ 25 101 (allA_of_3_0 25
  25 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 101 (allA_succ_of_accept 23 24 101
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 101 (accept_3_2 22 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  24 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 24 101 (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 24 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 101 (accept_3_2 19 24 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 101 (Polychromatic418967fa.accept_19_18_5_6_1_2004 18 24
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 101
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 24 101 (accept_3_2 16 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  24 101 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 24 101 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 24 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 101 (accept_3_2 13 24 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 24 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 101
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 11 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 101 (accept_3_2 10 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  24 101 (Polychromatic418967fa.accept_21_9_3_17_1_4365 9 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 24 101 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 24 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 101 (accept_3_2 7 24 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 101 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 24 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 101
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 101 (accept_3_2 4 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24
  101 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 101 (Polychromatic418967fa.accept_13_2_11_10_1_1881 2 24 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 101 (accept_3_2 1 24 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 101)))))))))))))))))))))))) (allB_succ 23 101 (allA_succ_of_accept 22 23 101 (accept_3_2 22
  23 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 101
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 23 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 23 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 101 (accept_3_2 19 23 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 101 (Polychromatic418967fa.accept_9_8_5_2_1_422 17
  23 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 101 (accept_3_2 16 23
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 101
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 23 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 101 (accept_3_2 13 23 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 101 (Polychromatic418967fa.accept_16_11_7_5_1_4364
  11 23 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 101 (accept_3_2 10
  23 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 101
  (Polychromatic418967fa.accept_17_9_6_16_1_3280 9 23 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 101 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 23 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 101 (accept_3_2 7 23 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 101 (Polychromatic418967fa.accept_7_5_2_3_1_106 5
  23 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 101 (accept_3_2 4 23 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 101 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 23
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 101 (accept_3_2 1 23 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  101))))))))))))))))))))))) (allB_succ 22 101 (allA_of_3_0 22 22 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 21 101 (allA_succ_of_accept 20 21 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 101 (accept_3_2 19 21 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 101 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 21
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 101
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 21 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 101 (accept_3_2 16 21 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 101 (accept_3_2 13 21 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 101 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 21 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 101
  (Polychromatic418967fa.accept_13_11_8_10_1_676 11 21 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 101 (accept_3_2 10 21 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 101 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 21 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 101 (accept_3_2 7 21 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 101 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 101
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 21 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 101 (accept_3_2 4 21 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  101 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 101 (accept_3_2 1 21 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 21 101))))))))))))))))))))) (allB_succ 20 101 (allA_succ_of_accept 19 20 101 (accept_3_2 19 20
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 101
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 20 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 101 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 20 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 101 (accept_3_2 16 20 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 101 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 20 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 101 (accept_3_2 13
  20 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 101
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 20 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 101 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 20 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 101 (accept_3_2 10 20 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 101 (Polychromatic418967fa.accept_13_8_7_10_1_4362
  8 20 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 101 (accept_3_2 7 20
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 101
  (Polychromatic418967fa.accept_15_6_5_11_1_2378 6 20 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 101 (Polychromatic418967fa.accept_19_5_1_6_1_4361 5 20 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 101 (accept_3_2 4 20 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  20 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 101 (accept_3_2 1 20 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 101)))))))))))))))))))) (allB_succ 19 101 (allA_of_3_0 19 19 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 18 101 (allA_succ_of_accept 17 18 101
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 18 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 18 101 (accept_3_2 16 18 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  18 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 18 101 (Polychromatic418967fa.accept_15_14_3_11_1_850 14 18 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 101 (accept_3_2 13 18 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 101 (Polychromatic418967fa.accept_17_12_1_16_1_4360 12 18
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 101
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 18 101 (accept_3_2 10 18 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  18 101 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 18 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 18 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 18 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 101 (accept_3_2 7 18 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 101 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 18 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 101
  (Polychromatic418967fa.accept_17_5_1_16_1_4359 5 18 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 18 101 (accept_3_2 4 18 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 101 (Polychromatic418967fa.accept_13_2_5_10_1_250 2 18 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 101 (accept_3_2 1 18 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 18 101)))))))))))))))))) (allB_succ 17 101 (allA_succ_of_accept 16 17 101 (accept_3_2 16 17 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  17 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 101
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 101 (accept_3_2 13 17 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 101 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 101 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 17 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 101 (accept_3_2 10 17 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 101 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 17 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 101
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 8 17 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 101 (accept_3_2 7 17 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  101 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 17 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 101 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 17 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 101 (accept_3_2 4 17 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 101 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 17 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 101 (Polychromatic418967fa.accept_18_2_17_11_1_3178
  2 17 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 101 (accept_3_2 1 17
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 101))))))))))))))))) (allB_succ 16 101 (allA_of_3_0 16 16
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 101 (allA_succ_of_accept 14 15 101
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 101 (accept_3_2 13 15 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 101 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 15 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 101 (accept_3_2 10 15 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 101
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 101 (accept_3_2 7 15 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 101 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 15 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 101 (accept_3_2 4 15 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 101 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 15 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 101 (accept_3_2 1 15 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 101))))))))))))))) (allB_succ 14 101 (allA_succ_of_accept 13 14
  101 (accept_3_2 13 14 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 101
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 14 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 101 (accept_3_2 10 14 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 101 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 101 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  14 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 101 (accept_3_2 7 14 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 101 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  14 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 101
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 14 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 101 (accept_3_2 4 14 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 101 (Polychromatic418967fa.accept_17_2_14_16_1_2187 2 14 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 101 (accept_3_2 1 14 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 101)))))))))))))) (allB_succ 13 101 (allA_of_3_0 13 13 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 101 (allA_succ_of_accept 11 12 101 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 12
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 101 (accept_3_2 10 12 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 101
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 12 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 101 (accept_3_2 7 12 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  101 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 12 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 101 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 101 (accept_3_2 4 12 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 101 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 12 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 12
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 101 (accept_3_2 1 12 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 101)))))))))))) (allB_succ 11 101 (allA_succ_of_accept 10 11 101
  (accept_3_2 10 11 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 101
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 11 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 101 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 11 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 101 (accept_3_2 7 11 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 101 (Polychromatic418967fa.accept_17_5_11_16_1_3257
  5 11 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 101 (accept_3_2 4 11
  101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 101
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 11 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 11 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 101 (accept_3_2 1 11 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 11 101))))))))))) (allB_succ 10 101 (allA_of_3_0 10 10 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 9 101 (allA_succ_of_accept 8 9 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 101 (accept_3_2 7 9 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 101 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 101
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 101 (accept_3_2 4 9 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 101
  (Polychromatic418967fa.accept_12_3_9_5_1_853 3 9 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 9 101 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 101 (accept_3_2 1 9 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 9 101))))))))) (allB_succ 8 101 (allA_succ_of_accept 7 8 101 (accept_3_2 7 8 101 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 101 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 8 101
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 101
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 8 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 101 (accept_3_2 4 8 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 101
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 101 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 8 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 101 (accept_3_2 1 8 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 101)))))))) (allB_succ 7 101 (allA_of_3_0 7 7 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 101 (allA_succ_of_accept 5 6 101 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 6 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 101 (accept_3_2 4 6 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 6 101 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 101 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 6
  101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 101 (accept_3_2 1 6 101
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 101)))))) (allB_succ 5 101 (allA_succ_of_accept 4 5 101
  (accept_3_2 4 5 101 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 101
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 5 101 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 101 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 5 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 101 (accept_3_2 1 5 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 101))))) (allB_succ 4 101 (allA_of_3_0 4 4 101 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 101 (allA_succ_of_accept 2 3 101 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 101 (accept_3_2 1 3 101 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 3 101))) (allB_succ 2 101 (allA_succ_of_accept 1 2 101 (accept_3_2 1 2 101 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 2 101)) (allB_two
  101)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


