-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch97
-- name    : Polychromatic418967fa_Branch97
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:59.478996+00:00
-- url     : https://prove2.me/theorems/cc2143d5-fba3-4f72-982c-73319d2c513c
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

def Polychromatic418967fa.branch_97 : allB 97 97 :=
  allB_succ' 2 96 97 (Eq.refl Bool.true) (allA_succ_of_accept 1 96 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 97)) (allB_succ' 3 95 97 (Eq.refl Bool.true)
  (allA_of_3_1 3 95 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 94 97 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 94 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 97 (accept_3_3 2 94 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 94 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 94 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 97)))) (allB_succ' 5 93 97 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 93 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 97 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 97 (accept_3_3 2 93 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 93 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 97))))) (allB_succ' 6 92 97 (Eq.refl
  Bool.true) (allA_of_3_1 6 92 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 91 97 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 91 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 97 (accept_3_3 5 91 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 91 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 91 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 97 (accept_3_3 2 91 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 97 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 91 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 97))))))) (allB_succ' 8 90 97 (Eq.refl
  Bool.true) (allA_succ_of_accept 7 90 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 97 (Polychromatic418967fa.accept_24_6_18_1_1_2584 6
  90 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 97 (accept_3_3 5 90 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 97 (Polychromatic418967fa.accept_11_4_2_9_1_496 4
  90 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 97 (accept_3_3 2 90 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 97
  (Polychromatic418967fa.accept_19_1_14_2_1_4134 1 90 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 97)))))))) (allB_succ' 9 89 97 (Eq.refl Bool.true) (allA_of_3_1 9 89 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 10 88 97 (Eq.refl Bool.true) (allA_succ_of_accept 9 88 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 97 (accept_3_3 8 88 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 97
  (Polychromatic418967fa.accept_16_7_8_1_1_3061 7 88 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 88 97 (Polychromatic418967fa.accept_15_6_13_7_1_222 6 88 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 97 (accept_3_3 5 88 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 88 97 (Polychromatic418967fa.accept_13_4_10_6_1_989 4 88 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 97 (accept_3_3 2 88 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 97 (Polychromatic418967fa.accept_18_1_16_7_1_2897 1
  88 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 97)))))))))) (allB_succ' 11 87 97
  (Eq.refl Bool.true) (allA_succ_of_accept 10 87 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 97
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 97 (accept_3_3 8 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 97
  (Polychromatic418967fa.accept_13_7_9_6_1_148 7 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 97 (accept_3_3 5 87 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 97 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 87 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 97 (accept_3_3 2 87 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 87 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 97))))))))))) (allB_succ' 12 86 97 (Eq.refl
  Bool.true) (allA_of_3_1 12 86 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 85 97 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 85 97 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 97 (accept_3_3 11 85 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 85 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 85 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 85
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 97 (accept_3_3 8 85 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 97 (Polychromatic418967fa.accept_14_7_1_13_1_357 7
  85 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 97
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 97 (accept_3_3 5 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 97
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 85 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 97 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 85 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 97 (accept_3_3 2 85 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 97))))))))))))) (allB_succ' 14 84 97 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 97 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 84 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 97 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 84 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 97 (accept_3_3 11 84 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 84
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 97
  (Polychromatic418967fa.accept_27_9_3_16_1_4133 9 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 84 97 (accept_3_3 8 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 97
  (Polychromatic418967fa.accept_20_7_4_17_1_4132 7 84 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 84 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 84 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 97 (accept_3_3 5 84 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 84 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 84 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 97 (Polychromatic418967fa.accept_10_3_4_7_1_353 3
  84 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 97 (accept_3_3 2 84 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 97)))))))))))))) (allB_succ' 15 83 97
  (Eq.refl Bool.true) (allA_of_3_1 15 83 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 82 97 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 82 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 97 (accept_3_3 14 82 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 82 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 97
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 97 (accept_3_3 11 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 82
  97 (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 97 (accept_3_3 8 82 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 82 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 82
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 97 (accept_3_3 5 82 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 82
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 82 97 (accept_3_3 2 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 97
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 82 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 97)))))))))))))))) (allB_succ' 17 81 97 (Eq.refl Bool.true) (allA_succ_of_accept 16 81 97
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 81 97 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 81 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 97 (accept_3_3 14 81 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 81 97 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 81 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 97 (Polychromatic418967fa.accept_7_5_4_6_1_167 12
  81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 97 (accept_3_3 11 81 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 97
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 97 (accept_3_3 8 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 97
  (Polychromatic418967fa.accept_19_7_5_2_1_2842 7 81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 97 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 81 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 97 (accept_3_3 5 81 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 97 (accept_3_3 2 81 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 97 (Polychromatic418967fa.accept_13_1_3_6_1_158 1
  81 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 97))))))))))))))))) (allB_succ' 18 80
  97 (Eq.refl Bool.true) (allA_of_3_1 18 80 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 79 97 (Eq.refl
  Bool.true) (allA_succ_of_accept 18 79 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 97 (accept_3_3 17 79 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 97 (Polychromatic418967fa.accept_13_3_1_6_1_509 16 79 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 97
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 97 (accept_3_3 14 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 79
  97 (Polychromatic418967fa.accept_17_13_11_12_1_4131 13 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 97 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 79 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 97 (accept_3_3 11 79 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 97
  (Polychromatic418967fa.accept_13_9_1_6_1_510 9 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 97 (accept_3_3 8 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 97
  (Polychromatic418967fa.accept_11_7_2_9_1_480 7 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 79 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 97 (accept_3_3 5 79 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 79 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 79 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 97 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 79 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 97 (accept_3_3 2 79 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 79 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 97))))))))))))))))))) (allB_succ' 20 78 97
  (Eq.refl Bool.true) (allA_succ_of_accept 19 78 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 97
  (Polychromatic418967fa.accept_21_18_15_13_1_4130 18 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 97 (accept_3_3 17 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78
  97 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 78 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 97 (accept_3_3 14 78 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 78 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 78 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 97 (Polychromatic418967fa.accept_7_5_1_6_1_163 12
  78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 97 (accept_3_3 11 78 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 10
  78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 78 97
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 97 (accept_3_3 8 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 78 97 (Polychromatic418967fa.accept_17_6_10_12_1_4129 6 78 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 97 (accept_3_3 5 78 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 78 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 78 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 97 (accept_3_3 2 78 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 97)))))))))))))))))))) (allB_succ' 21 77
  97 (Eq.refl Bool.true) (allA_of_3_1 21 77 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 76 97 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 76 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 97 (accept_3_3 20 76 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 97
  (Polychromatic418967fa.accept_13_5_11_6_1_505 18 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 97 (accept_3_3 17 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 76
  97 (Polychromatic418967fa.accept_18_16_4_7_1_2927 16 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 97 (accept_3_3 14 76 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 97 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 76 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 97 (accept_3_3 11 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 76
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 76 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 97 (accept_3_3 8 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 76 97 (Polychromatic418967fa.accept_14_7_6_13_1_4111 7 76 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 76 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 97 (accept_3_3 5 76 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76 97 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 76 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 76 97 (accept_3_3 2 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 97
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 97)))))))))))))))))))))) (allB_succ' 23 75 97 (Eq.refl Bool.true) (allA_succ_of_accept 22 75 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 75 97 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 97 (accept_3_3 20 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 75 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 75 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 97 (accept_3_3 17 75 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 97
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 97 (accept_3_3 14 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75
  97 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 97 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 97 (accept_3_3 11 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 75 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 97 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 97 (accept_3_3 8 75 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 97 (Polychromatic418967fa.accept_23_7_6_5_1_4128 7
  75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 97 (accept_3_3 5 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 97
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 97 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 97 (accept_3_3 2 75 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 75 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 97))))))))))))))))))))))) (allB_succ' 24 74 97 (Eq.refl
  Bool.true) (allA_of_3_1 24 74 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 73 97 (Eq.refl Bool.true)
  (allA_succ_of_accept 24 73 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 97 (accept_3_3 23 73 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 73 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 73 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 21
  73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 97 (accept_3_3 20 73 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 97 (Polychromatic418967fa.accept_23_19_4_5_1_1329
  19 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 97
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 97 (accept_3_3 17 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 73
  97 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 73 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 73 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 97 (accept_3_3 14 73 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 73 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 97 (accept_3_3 11 73 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 97 (Polychromatic418967fa.accept_14_10_3_13_1_1530
  10 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 97
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 97 (accept_3_3 8 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 97
  (Polychromatic418967fa.accept_17_7_5_12_1_1997 7 73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 97 (accept_3_3 5 73 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 97 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 73 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 73
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 97 (accept_3_3 2 73 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 97 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1
  73 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 97)))))))))))))))))))))))))
  (allB_succ' 26 72 97 (Eq.refl Bool.true) (allA_succ_of_accept 25 72 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 25
  72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 97
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 97 (accept_3_3 23 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72
  97 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 72 97 (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 72 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 97 (accept_3_3 20 72 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 72 97 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 72 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 18
  72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 97 (accept_3_3 17 72 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 97 (Polychromatic418967fa.accept_21_16_9_13_1_4127
  16 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 97
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 72 97 (accept_3_3 14 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72
  97 (Polychromatic418967fa.accept_19_13_15_2_1_4126 13 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 72 97 (Polychromatic418967fa.accept_13_12_7_6_1_1015 12 72 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 97 (accept_3_3 11 72 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 97 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 72 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 97
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 72 97 (accept_3_3 8 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 97
  (Polychromatic418967fa.accept_16_7_8_1_1_3061 7 72 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 72 97 (Polychromatic418967fa.accept_15_6_12_7_1_1360 6 72 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 97 (accept_3_3 5 72 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 72 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 72 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 97 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 97 (accept_3_3 2 72 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 97)))))))))))))))))))))))))) (allB_succ'
  27 71 97 (Eq.refl Bool.true) (allA_of_3_1 27 71 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 70 97
  (Eq.refl Bool.true) (allA_succ_of_accept 27 70 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 97 (accept_3_3 26 70 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 97 (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 70 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 97
  (Polychromatic418967fa.accept_11_2_4_9_1_484 24 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 97 (accept_3_3 23 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 70
  97 (Polychromatic418967fa.accept_18_4_16_7_1_1873 22 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 97 (accept_3_3 20 70 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 97
  (Polychromatic418967fa.accept_15_3_10_7_1_2196 18 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 97 (accept_3_3 17 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70
  97 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 70 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 97 (accept_3_3 14 70 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 70 97 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 70 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 97 (Polychromatic418967fa.accept_13_12_5_6_1_1050
  12 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 97 (accept_3_3 11 70
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 97
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 10 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 70 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 97 (accept_3_3 8 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 70 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 97 (Polychromatic418967fa.accept_17_6_2_12_1_1992 6 70 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 97 (accept_3_3 5 70 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 97 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 70 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 97 (accept_3_3 2 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 97
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 70 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 97)))))))))))))))))))))))))))) (allB_succ' 29 69 97 (Eq.refl Bool.true) (allA_succ_of_accept 28 69 97
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 69 97 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 97 (accept_3_3 26 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 69 97 (Polychromatic418967fa.accept_16_9_5_1_1_1259 25 69 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 97 (Polychromatic418967fa.accept_13_11_4_6_1_1006
  24 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 97 (accept_3_3 23 69
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 97 (Polychromatic418967fa.accept_6_4_3_1_1_57
  22 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 97
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 97 (accept_3_3 20 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69
  97 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 69 97 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 97 (accept_3_3 17 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 69 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 97 (Polychromatic418967fa.accept_12_3_9_1_1_290 15
  69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 97 (accept_3_3 14 69 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 13
  69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 97
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 97 (accept_3_3 11 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 69 97 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 97 (accept_3_3 8 69 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 69 97 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 69 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 97 (Polychromatic418967fa.accept_11_6_3_9_1_906 6
  69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 97 (accept_3_3 5 69 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 97
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 97 (accept_3_3 2 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 97
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 69 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 97))))))))))))))))))))))))))))) (allB_succ' 30 68 97 (Eq.refl Bool.true) (allA_of_3_1 30 68 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 67 97 (Eq.refl Bool.true) (allA_succ_of_accept 30 67 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 97 (accept_3_3 29 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 67
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 67 97 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 67 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 97 (accept_3_3 26 67 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 67 97 (Polychromatic418967fa.accept_13_12_2_6_1_2396 25 67 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 24
  67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 97 (accept_3_3 23 67 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 97 (accept_3_3 20 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67
  97 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 67 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 97 (accept_3_3 17 67 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 67 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 67 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 15
  67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 97 (accept_3_3 14 67 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 97 (Polychromatic418967fa.accept_16_13_3_1_1_2100
  13 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 97
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 97 (accept_3_3 11 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 67
  97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 67 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 67 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 97 (accept_3_3 8 67 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 67 97 (Polychromatic418967fa.accept_21_7_4_13_1_4125 7 67 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 97 (accept_3_3 5 67 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 97 (Polychromatic418967fa.accept_13_4_2_6_1_1043 4
  67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 97
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 97 (accept_3_3 2 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 97
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 67 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 67 97))))))))))))))))))))))))))))))) (allB_succ' 32 66 97 (Eq.refl Bool.true) (allA_succ_of_accept 31 66 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 66 97 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 66 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 97 (accept_3_3 29 66 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 66 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 66 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  66 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 97 (accept_3_3 26 66 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 97 (Polychromatic418967fa.accept_7_4_3_6_1_340 25
  66 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 97
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 66 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 97 (accept_3_3 23 66 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66
  97 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 66 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 66 97 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 66 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 97 (accept_3_3 20 66 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 66 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 97 (Polychromatic418967fa.accept_7_4_3_6_1_340 18
  66 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 97 (accept_3_3 17 66 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 97 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 66
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 97 (accept_3_3 14 66 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66
  97 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 66 97 (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 66 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 97 (accept_3_3 11 66 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 66 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 66 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 97 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 97 (accept_3_3 8 66 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 97
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 66 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 97 (accept_3_3 5 66 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 97
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 66 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 66 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 97 (accept_3_3 2 66 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 66 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 66 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 97)))))))))))))))))))))))))))))))) (allB_succ' 33 65 97 (Eq.refl
  Bool.true) (allA_of_3_1 33 65 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 64 97 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 64 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 97 (accept_3_3 32 64 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 64 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 30
  64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 97 (accept_3_3 29 64 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 97 (Polychromatic418967fa.accept_13_2_12_6_1_2394
  28 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 97 (accept_3_3 26 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 64
  97 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 64 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 97 (accept_3_3 23 64 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 64 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 97 (accept_3_3 20 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 64
  97 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 64 97 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 64 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 97 (accept_3_3 17 64 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 64 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 64 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 97 (accept_3_3 14 64 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 97
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 97 (accept_3_3 11 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64
  97 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 97 (accept_3_3 8 64 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 64 97 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 64 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 64
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 97 (accept_3_3 5 64 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 64
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 97 (accept_3_3 2 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 97
  (Polychromatic418967fa.accept_10_1_4_7_1_374 1 64 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 97)))))))))))))))))))))))))))))))))) (allB_succ' 35 63 97 (Eq.refl Bool.true) (allA_succ_of_accept 34 63
  97 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 63 97 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 63 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 97 (accept_3_3 32 63 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 63 97 (Polychromatic418967fa.accept_13_5_11_6_1_505 31 63 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 97 (accept_3_3 29 63 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 97
  (Polychromatic418967fa.accept_15_12_3_7_1_4123 27 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 97 (accept_3_3 26 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63
  97 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 63 97 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 63 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 97 (accept_3_3 23 63 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 63 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 97 (Polychromatic418967fa.accept_11_10_8_9_1_492
  21 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 97 (accept_3_3 20 63
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 97 (Polychromatic418967fa.accept_15_4_3_7_1_713
  19 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 97 (accept_3_3 17 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 63 97 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 63 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 97 (accept_3_3 14 63 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 63 97 (Polychromatic418967fa.accept_19_13_6_2_1_4124 13 63 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 97 (Polychromatic418967fa.accept_15_12_3_7_1_4123
  12 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 97 (accept_3_3 11 63
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 97
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 97 (accept_3_3 8 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 97
  (Polychromatic418967fa.accept_26_7_11_19_1_4122 7 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 97 (accept_3_3 5 63 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 97 (Polychromatic418967fa.accept_18_3_9_7_1_1839 3 63 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 97 (accept_3_3 2 63 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 97 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 63 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 97)))))))))))))))))))))))))))))))))))
  (allB_succ' 36 62 97 (Eq.refl Bool.true) (allA_of_3_1 36 62 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37
  61 97 (Eq.refl Bool.true) (allA_succ_of_accept 36 61 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 61 97 (accept_3_3 35 61 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 61 97 (Polychromatic418967fa.accept_10_4_1_7_1_371 34 61 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 97
  (Polychromatic418967fa.accept_13_7_9_6_1_148 33 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 61 97 (accept_3_3 32 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61
  97 (Polychromatic418967fa.accept_19_12_4_2_1_4121 31 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 61 97 (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 61 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 97 (accept_3_3 29 61 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 61 97 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 61 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 97
  (Polychromatic418967fa.accept_13_1_9_6_1_146 27 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 61 97 (accept_3_3 26 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61
  97 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 61 97 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 61 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 97 (accept_3_3 23 61 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 61 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 61 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 97 (Polychromatic418967fa.accept_15_6_1_7_1_4079
  21 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 97 (accept_3_3 20 61
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 97
  (Polychromatic418967fa.accept_16_3_13_1_1_1206 19 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 61 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 61 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 97 (accept_3_3 17 61 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 61 97 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 61 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 97 (accept_3_3 14 61 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 97 (Polychromatic418967fa.accept_23_13_15_5_1_4120
  13 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 97
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 97 (accept_3_3 11 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61
  97 (Polychromatic418967fa.accept_13_10_9_6_1_1026 10 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 97 (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 61 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 97 (accept_3_3 8 61 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 61 97 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 61 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 97 (Polychromatic418967fa.accept_10_6_1_7_1_342 6
  61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 97 (accept_3_3 5 61 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 61
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 97
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 97 (accept_3_3 2 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 97
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 61 97))))))))))))))))))))))))))))))))))))) (allB_succ' 38 60 97 (Eq.refl Bool.true) (allA_succ_of_accept 37
  60 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 97 (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 60 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 97 (accept_3_3 35 60 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 97 (Polychromatic418967fa.accept_16_2_12_1_1_3086 34 60 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 97
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 60 97 (accept_3_3 32 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60
  97 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 60 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 60 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 97 (accept_3_3 29 60 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 60 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 60 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 97 (Polychromatic418967fa.accept_13_1_8_6_1_1016
  27 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 97 (accept_3_3 26 60
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 97
  (Polychromatic418967fa.accept_19_6_3_2_1_4119 25 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 60 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 60 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 97 (accept_3_3 23 60 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 60 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 60 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 97 (Polychromatic418967fa.accept_8_5_4_1_1_111 21
  60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 97 (accept_3_3 20 60 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 97 (Polychromatic418967fa.accept_7_5_4_6_1_167 19
  60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 97
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 97 (accept_3_3 17 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60
  97 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 60 97 (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 60 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 97 (accept_3_3 14 60 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 60 97 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 60 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 97 (Polychromatic418967fa.accept_7_5_4_6_1_167 12
  60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 97 (accept_3_3 11 60 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 10
  60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 60 97
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 97 (accept_3_3 8 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 97
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 60 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 60 97 (Polychromatic418967fa.accept_19_6_3_2_1_4119 6 60 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 97 (accept_3_3 5 60 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 60 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 60 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 97 (accept_3_3 2 60 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 97))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 59 97 (Eq.refl Bool.true) (allA_of_3_1 39 59 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40
  58 97 (Eq.refl Bool.true) (allA_succ_of_accept 39 58 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 97 (accept_3_3 38 58 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 97
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 97 (accept_3_3 35 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58
  97 (Polychromatic418967fa.accept_18_16_4_7_1_2927 34 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 97 (accept_3_3 32 58 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 97 (accept_3_3 29 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 58 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 97 (accept_3_3 26 58 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 58 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 58 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 97 (Polychromatic418967fa.accept_7_3_2_6_1_56 24
  58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 97 (accept_3_3 23 58 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 22
  58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 97 (accept_3_3 20 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 58
  97 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 58 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 58 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 97 (accept_3_3 17 58 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 58 97 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 58 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 97 (accept_3_3 14 58 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 97 (Polychromatic418967fa.accept_18_13_4_7_1_4086
  13 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 97 (accept_3_3 11 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58
  97 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 58 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 97 (accept_3_3 8 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 58 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 58 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 97 (accept_3_3 5 58 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 58 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 58 97 (accept_3_3 2 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 97
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 58 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 97)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 57 97 (Eq.refl Bool.true) (allA_succ_of_accept
  40 57 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 97 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 57 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 97 (accept_3_3 38 57 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 57 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 97
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 97 (accept_3_3 35 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 57 97 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 97 (accept_3_3 32 57 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 57 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 57 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 30
  57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 97 (accept_3_3 29 57 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 97
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 97 (accept_3_3 26 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57
  97 (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 97 (accept_3_3 23 57 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 97
  (Polychromatic418967fa.accept_14_7_1_13_1_357 21 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 97 (accept_3_3 20 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57
  97 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 97 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 57 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 97 (accept_3_3 17 57 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 97 (accept_3_3 14 57 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 97
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 97 (accept_3_3 11 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 57 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 97 (accept_3_3 8 57 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 57 97 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 57 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 97 (accept_3_3 5 57 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 97
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 97 (accept_3_3 2 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 97
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 57 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 97))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 56 97 (Eq.refl Bool.true) (allA_of_3_1 42 56
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 55 97 (Eq.refl Bool.true) (allA_succ_of_accept 42 55 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 97 (accept_3_3 41 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55
  97 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 55 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 55 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 97 (accept_3_3 38 55 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 55 97 (Polychromatic418967fa.accept_23_14_9_5_1_4118 37 55 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 97 (Polychromatic418967fa.accept_13_10_3_6_1_1003
  36 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 97 (accept_3_3 35 55
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 34
  55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 97
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 97 (accept_3_3 32 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55
  97 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 55 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 97 (accept_3_3 29 55 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 55 97 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 55 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 97 (Polychromatic418967fa.accept_13_1_3_6_1_158 27
  55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 97 (accept_3_3 26 55 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 97 (Polychromatic418967fa.accept_17_8_4_12_1_1994
  25 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 97
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 97 (accept_3_3 23 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55
  97 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 55 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 55 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 97 (accept_3_3 20 55 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 55 97 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 55 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 97 (accept_3_3 17 55 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 97 (Polychromatic418967fa.accept_15_1_10_7_1_4087
  16 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 97
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 97 (accept_3_3 14 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55
  97 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 55 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 55 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 97 (accept_3_3 11 55 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 55 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 97 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9
  55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 97 (accept_3_3 8 55 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 97 (Polychromatic418967fa.accept_17_7_4_12_1_4084 7
  55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 97 (accept_3_3 5 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 97
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 55 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 55 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 97 (accept_3_3 2 55 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 97 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 55 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 97))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 54
  97 (Eq.refl Bool.true) (allA_succ_of_accept 43 54 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 97
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 97 (accept_3_3 41 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54
  97 (Polychromatic418967fa.accept_13_1_2_6_1_515 40 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 54 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 97 (accept_3_3 38 54 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 54 97 (Polychromatic418967fa.accept_16_5_6_1_1_2118 37 54 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 36
  54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 97 (accept_3_3 35 54 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 97 (Polychromatic418967fa.accept_11_1_10_9_1_871
  34 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 97
  (Polychromatic418967fa.accept_10_3_4_7_1_353 33 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 54 97 (accept_3_3 32 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54
  97 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 54 97 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 54 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 97 (accept_3_3 29 54 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 54 97 (Polychromatic418967fa.accept_15_13_9_7_1_2194 28 54 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 97 (accept_3_3 26 54 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 25
  54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 97
  (Polychromatic418967fa.accept_17_7_3_12_1_4098 24 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 97 (accept_3_3 23 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54
  97 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 54 97 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 54 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 97 (accept_3_3 20 54 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 54 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 18
  54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 97 (accept_3_3 17 54 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 97 (Polychromatic418967fa.accept_15_1_9_7_1_3130
  16 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 54 97 (accept_3_3 14 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54
  97 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 54 97 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 54 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 97 (accept_3_3 11 54 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 54 97 (Polychromatic418967fa.accept_13_10_2_6_1_1044 10 54 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 97 (Polychromatic418967fa.accept_13_9_2_6_1_514 9
  54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 97 (accept_3_3 8 54 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 97
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 6 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 97 (accept_3_3 5 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 97
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 54 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 54 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 97 (accept_3_3 2 54 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 54 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 54 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 97)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 53
  97 (Eq.refl Bool.true) (allA_of_3_1 45 53 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 52 97 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 52 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 97 (accept_3_3 44 52 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 97 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 52 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 97
  (Polychromatic418967fa.accept_19_4_14_2_1_4117 42 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 97 (accept_3_3 41 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52
  97 (Polychromatic418967fa.accept_16_8_4_1_1_2102 40 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 52 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 97 (accept_3_3 38 52 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 52 97 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 52 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 97 (Polychromatic418967fa.accept_19_17_14_2_1_4116
  36 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 97 (accept_3_3 35 52
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 97 (Polychromatic418967fa.accept_10_4_2_7_1_373
  34 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 97 (accept_3_3 32 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 52
  97 (Polychromatic418967fa.accept_14_3_10_13_1_339 31 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 97 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 52 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 97 (accept_3_3 29 52 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 97 (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 52 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 97 (accept_3_3 26 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 52
  97 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 52 97 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 52 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 97 (accept_3_3 23 52 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 52 97 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 52 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 97 (accept_3_3 20 52 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 97 (Polychromatic418967fa.accept_10_9_2_7_1_1096
  19 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 97
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 97 (accept_3_3 17 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52
  97 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 52 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 97 (accept_3_3 14 52 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 52 97 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 52 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 97 (Polychromatic418967fa.accept_16_12_4_1_1_1257
  12 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 97 (accept_3_3 11 52
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 97
  (Polychromatic418967fa.accept_11_10_8_9_1_492 10 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 52 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 97 (accept_3_3 8 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 52 97 (Polychromatic418967fa.accept_19_7_14_2_1_4095 7 52 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 97 (Polychromatic418967fa.accept_17_6_1_12_1_4115 6 52 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 97 (accept_3_3 5 52 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52 97 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 52 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 52 97 (accept_3_3 2 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 97
  (Polychromatic418967fa.accept_18_1_16_7_1_2897 1 52 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 97)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 51 97 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 51 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 97 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 97 (accept_3_3 44 51 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 43
  51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 97 (accept_3_3 41 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 51 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 97 (accept_3_3 38 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 51 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 51 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 36
  51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 97 (accept_3_3 35 51 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 97
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 97 (accept_3_3 32 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51
  97 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 51 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 97 (accept_3_3 29 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 51 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 97 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  27 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 97 (accept_3_3 26 51
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 97 (Polychromatic418967fa.accept_7_4_2_6_1_337
  25 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 97
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 97 (accept_3_3 23 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51
  97 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 51 97 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 97 (accept_3_3 20 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 51 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 51 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 97 (accept_3_3 17 51 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 97
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 97 (accept_3_3 14 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51
  97 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 51 97 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 97 (accept_3_3 11 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 97 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 97 (accept_3_3 8 51 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 97 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7
  51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 97 (accept_3_3 5 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 97
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 97 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 97 (accept_3_3 2 51 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 51 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 97))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48
  50 97 (Eq.refl Bool.true) (allA_of_3_1 48 50 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 97
  (allA_succ_of_accept 48 49 97 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 97 (accept_3_3 47 49 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 49 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 97 (Polychromatic418967fa.accept_22_1_5_9_1_4114
  45 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 97 (accept_3_3 44 49
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 97
  (Polychromatic418967fa.accept_13_4_10_6_1_989 43 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 97 (accept_3_3 41 49 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 97 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 49 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 97 (Polychromatic418967fa.accept_9_3_4_7_1_89 39
  49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 97 (accept_3_3 38 49 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 97
  (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 97 (accept_3_3 35 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49
  97 (Polychromatic418967fa.accept_14_6_7_13_1_3158 34 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 49 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 97 (accept_3_3 32 49 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 97 (Polychromatic418967fa.accept_13_5_10_6_1_2361 31 49 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 97 (accept_3_3 29 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 49 97 (Polychromatic418967fa.accept_15_12_4_7_1_3097 27 49 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 97 (accept_3_3 26 49 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 49 97 (Polychromatic418967fa.accept_13_12_10_6_1_3212 25 49 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 24
  49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 97 (accept_3_3 23 49 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 97 (Polychromatic418967fa.accept_10_2_9_7_1_720 22
  49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 97 (accept_3_3 20 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 97 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 49 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 97 (accept_3_3 17 49 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 97 (Polychromatic418967fa.accept_13_3_10_6_1_2382 16 49 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 15
  49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 97 (accept_3_3 14 49 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 97 (Polychromatic418967fa.accept_19_13_11_2_1_4112
  13 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 97 (accept_3_3 11 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 49 97 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 49 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 97 (accept_3_3 8 49 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 49 97 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 49 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 97 (accept_3_3 5 49 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 97 (Polychromatic418967fa.accept_13_4_10_6_1_989 4
  49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 97 (accept_3_3 2 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 97
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 97))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 97 (allA_succ_of_accept 47 48 97
  (accept_3_3 47 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 97
  (Polychromatic418967fa.accept_9_1_3_7_1_6 46 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 97 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 48 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 97 (accept_3_3 44 48 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 97 (Polychromatic418967fa.accept_13_4_9_6_1_2376 43 48 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 42
  48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 97 (accept_3_3 41 48 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 40
  48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 48 97
  (Polychromatic418967fa.accept_10_9_8_7_1_714 39 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 48 97 (accept_3_3 38 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48
  97 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 48 97 (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 48 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 97 (accept_3_3 35 48 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 48 97 (Polychromatic418967fa.accept_15_4_3_7_1_713 34 48 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 48 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 33
  48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 97 (accept_3_3 32 48 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 31
  48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 97
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 97 (accept_3_3 29 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48
  97 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 48 97 (Polychromatic418967fa.accept_13_1_9_6_1_146 27 48 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 97 (accept_3_3 26 48 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 48 97 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 48 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 24
  48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 97 (accept_3_3 23 48 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 22
  48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 97
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 48 97 (accept_3_3 20 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48
  97 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 48 97 (Polychromatic418967fa.accept_19_18_10_2_1_2850 18 48 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 97 (accept_3_3 17 48 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 48 97 (Polychromatic418967fa.accept_13_3_9_6_1_502 16 48 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 97 (accept_3_3 14 48 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 97
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 97 (accept_3_3 11 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48
  97 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 48 97 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 48 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 97 (accept_3_3 8 48 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 48 97 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 48 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 48
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 97 (accept_3_3 5 48 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 48
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48 97
  (Polychromatic418967fa.accept_13_3_9_6_1_502 3 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 97 (accept_3_3 2 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 97
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 97)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 97 (allA_of_3_1 47 47 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 97 (allA_succ_of_accept 45 46 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 97 (accept_3_3 44 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 46
  97 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 46 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 46 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 97 (accept_3_3 41 46 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 46 97 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 46 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 97 (accept_3_3 38 46 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 46 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 37
  46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 97
  (Polychromatic418967fa.accept_15_6_1_7_1_4079 36 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 46 97 (accept_3_3 35 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46
  97 (Polychromatic418967fa.accept_19_15_8_2_1_4110 34 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 46 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 97 (accept_3_3 32 46 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 46 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 97
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 46 97 (accept_3_3 29 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46
  97 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 97 (accept_3_3 26 46 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 97 (Polychromatic418967fa.accept_13_12_7_6_1_1015 25 46 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 24
  46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 97 (accept_3_3 23 46 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 22
  46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 97 (accept_3_3 20 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 46
  97 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 46 97 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 46 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 97 (accept_3_3 17 46 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 46 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 46 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 97 (accept_3_3 14 46 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 46 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 97
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 46 97 (accept_3_3 11 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46
  97 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 46 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 97 (accept_3_3 8 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 46 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 46 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 97 (accept_3_3 5 46 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 46 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 97 (accept_3_3 2 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 97
  (Polychromatic418967fa.accept_10_1_6_7_1_710 1 46 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 97)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 97 (allA_succ_of_accept 44 45 97
  (accept_3_3 44 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 97
  (Polychromatic418967fa.accept_10_3_5_7_1_330 43 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 97 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 45 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 97 (accept_3_3 41 45 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 97 (Polychromatic418967fa.accept_7_4_3_6_1_340 39
  45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 97 (accept_3_3 38 45 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 97 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 45
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 97
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 97 (accept_3_3 35 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 45 97 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 45 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 97 (accept_3_3 32 45 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 45 97 (Polychromatic418967fa.accept_17_14_11_12_1_4109 31 45 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 97
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 97 (accept_3_3 29 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 97 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 45 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 97 (accept_3_3 26 45 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 45 97 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 45 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 97 (Polychromatic418967fa.accept_14_10_3_13_1_1530
  24 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 97 (accept_3_3 23 45
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 97 (Polychromatic418967fa.accept_6_4_3_1_1_57
  22 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 97
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 97 (accept_3_3 20 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45
  97 (Polychromatic418967fa.accept_16_3_13_1_1_1206 19 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 97 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 97 (accept_3_3 17 45 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 97
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 97 (accept_3_3 14 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45
  97 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 97 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 45 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 97 (accept_3_3 11 45 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 45 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 45 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 97 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 97 (accept_3_3 8 45 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 97 (Polychromatic418967fa.accept_27_7_18_16_1_4108
  7 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 97
  (Polychromatic418967fa.accept_17_6_11_12_1_4107 6 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 97 (accept_3_3 5 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 97
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 97 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 45 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 97 (accept_3_3 2 45 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 97 (Polychromatic418967fa.accept_19_1_7_2_1_4106 1 45 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 97))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 97
  (allA_of_3_1 44 44 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 97 (allA_succ_of_accept 42 43 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 97 (accept_3_3 41 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43
  97 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 43 97 (Polychromatic418967fa.accept_15_9_13_7_1_1361 39 43 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 97 (accept_3_3 38 43 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 43 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 43 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 97 (Polychromatic418967fa.accept_10_6_3_7_1_2197
  36 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 97 (accept_3_3 35 43
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 34
  43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 97
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 97 (accept_3_3 32 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43
  97 (Polychromatic418967fa.accept_13_5_4_6_1_2371 31 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 43 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 97 (accept_3_3 29 43 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 43 97 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 43 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 97 (Polychromatic418967fa.accept_19_8_5_2_1_4105
  27 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 97 (accept_3_3 26 43
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 97
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 43 97 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 43 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 97 (accept_3_3 23 43 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 43 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 97 (Polychromatic418967fa.accept_14_7_1_13_1_357
  21 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 97 (accept_3_3 20 43
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 97 (Polychromatic418967fa.accept_7_5_1_6_1_163
  19 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 97 (accept_3_3 17 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43
  97 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 43 97 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 43 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 97 (accept_3_3 14 43 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 43 97 (Polychromatic418967fa.accept_22_13_21_9_1_4104 13 43 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 97 (Polychromatic418967fa.accept_7_5_1_6_1_163 12
  43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 97 (accept_3_3 11 43 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 97
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 97 (accept_3_3 8 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 97
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 97 (accept_3_3 5 43 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 43 97 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 43 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 97 (Polychromatic418967fa.accept_19_3_5_2_1_4103 3 43 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 97 (accept_3_3 2 43 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 97 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 43 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  97))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 97 (allA_succ_of_accept 41 42 97 (accept_3_3 41 42 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 40
  42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 42 97 (accept_3_3 38 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42
  97 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 42 97 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 42 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 97 (accept_3_3 35 42 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 42 97 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 42 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 97 (Polychromatic418967fa.accept_15_3_12_7_1_1346
  33 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 97 (accept_3_3 32 42
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 97 (Polychromatic418967fa.accept_4_3_2_1_1_50
  31 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 97
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 97 (accept_3_3 29 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42
  97 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 42 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 97 (accept_3_3 26 42 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 42 97 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 42 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 97 (Polychromatic418967fa.accept_10_4_2_7_1_373 24
  42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 97 (accept_3_3 23 42 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 22
  42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 42 97
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 42 97 (accept_3_3 20 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42
  97 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 42 97 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 42 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 97 (accept_3_3 17 42 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 42 97 (Polychromatic418967fa.accept_19_16_4_2_1_4102 16 42 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 97 (accept_3_3 14 42 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 13
  42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 97
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 97 (accept_3_3 11 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42
  97 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 42 97 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 42 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 97 (accept_3_3 8 42 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 42 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 97 (Polychromatic418967fa.accept_15_6_12_7_1_1360 6
  42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 97 (accept_3_3 5 42 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 42
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 97 (accept_3_3 2 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 97
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 97)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 97 (allA_of_3_1 41 41 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 40 97 (allA_succ_of_accept 39 40 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 40 97 (accept_3_3 38 40 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 40 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 97
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 40 97 (accept_3_3 35 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40
  97 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 40 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 97 (accept_3_3 32 40 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 40 97 (Polychromatic418967fa.accept_13_5_1_6_1_2367 31 40 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 40 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 40 97 (accept_3_3 29 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 40
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 40 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 97 (accept_3_3 26 40 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 40 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 40 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 40 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 24
  40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 97 (accept_3_3 23 40 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 22
  40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 97 (accept_3_3 20 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 40
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 40 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 40 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 97 (accept_3_3 17 40 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 40 97 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 40 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 40 97 (accept_3_3 14 40 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 97 (Polychromatic418967fa.accept_11_2_7_9_1_890 13
  40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 97 (accept_3_3 11 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 40 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 97 (accept_3_3 8 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 40 97 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 40 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 40 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 97 (accept_3_3 5 40 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 40 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 97 (accept_3_3 2 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 97
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 40 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 97)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 97 (allA_succ_of_accept 38 39 97 (accept_3_3 38
  39 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 97
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 97 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 39 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 97 (accept_3_3 35 39 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 97 (Polychromatic418967fa.accept_7_5_4_6_1_167 33
  39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 97 (accept_3_3 32 39 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 31
  39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 97 (accept_3_3 29 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 39 97 (Polychromatic418967fa.accept_17_10_5_12_1_4101 27 39 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 97 (accept_3_3 26 39 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 39 97 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 39 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 24
  39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 97 (accept_3_3 23 39 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 97
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 97 (accept_3_3 20 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39
  97 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 97 (accept_3_3 17 39 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 39 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 97 (accept_3_3 14 39 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 97
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 97 (accept_3_3 11 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39
  97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 39 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 39 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 97 (accept_3_3 8 39 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 39 97 (Polychromatic418967fa.accept_17_7_5_12_1_1997 7 39 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 97 (accept_3_3 5 39 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 97
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 39 97 (accept_3_3 2 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 97
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 39 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 39 97))))))))))))))))))))))))))))))))))))))) (allB_succ 38 97 (allA_of_3_1 38 38 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 37 97 (allA_succ_of_accept 36 37 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 97 (accept_3_3 35 37 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 97 (Polychromatic418967fa.accept_13_8_11_6_1_1035
  34 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 97
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 97 (accept_3_3 32 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37
  97 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 97 (accept_3_3 29 37 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 97 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 37 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 97 (Polychromatic418967fa.accept_21_6_16_13_1_4100
  27 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 97 (accept_3_3 26 37
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 97 (Polychromatic418967fa.accept_7_4_2_6_1_337
  25 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 97
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 97 (accept_3_3 23 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37
  97 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 37 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 37 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 97 (accept_3_3 20 37 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 37 97 (Polychromatic418967fa.accept_21_19_16_13_1_4099 19 37 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 97
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 97 (accept_3_3 17 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37
  97 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 37 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 97 (accept_3_3 14 37 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 37 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 97
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 97 (accept_3_3 11 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37
  97 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 37 97 (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 37 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 97 (accept_3_3 8 37 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 37 97 (Polychromatic418967fa.accept_17_7_3_12_1_4098 7 37 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 37
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 97 (accept_3_3 5 37 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 37
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 97
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 97 (accept_3_3 2 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 97
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 97))))))))))))))))))))))))))))))))))))) (allB_succ 36 97 (allA_succ_of_accept 35 36 97 (accept_3_3 35 36
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 97
  (Polychromatic418967fa.accept_19_15_17_2_1_4097 34 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 36 97 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 97 (accept_3_3 32 36 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 36 97 (Polychromatic418967fa.accept_10_1_6_7_1_710 31 36 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 30
  36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 97 (accept_3_3 29 36 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 97 (Polychromatic418967fa.accept_11_6_3_9_1_906 28
  36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 97
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 36 97 (accept_3_3 26 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36
  97 (Polychromatic418967fa.accept_13_12_10_6_1_3212 25 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 36 97 (Polychromatic418967fa.accept_16_8_4_1_1_2102 24 36 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 97 (accept_3_3 23 36 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 97 (Polychromatic418967fa.accept_13_9_10_6_1_1028 22 36 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 97
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 36 97 (accept_3_3 20 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36
  97 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 36 97 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 36 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 97 (accept_3_3 17 36 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 36 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 36 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 97 (Polychromatic418967fa.accept_13_2_10_6_1_1676
  15 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 97 (accept_3_3 14 36
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 97 (Polychromatic418967fa.accept_8_5_4_1_1_111
  13 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 97
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 97 (accept_3_3 11 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36
  97 (Polychromatic418967fa.accept_17_10_2_12_1_1070 10 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 97 (accept_3_3 8 36 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 36 97 (Polychromatic418967fa.accept_14_7_8_13_1_3161 7 36 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 97 (Polychromatic418967fa.accept_11_6_3_9_1_906 6
  36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 97 (accept_3_3 5 36 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 97 (Polychromatic418967fa.accept_13_4_10_6_1_989 4
  36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 97
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 97 (accept_3_3 2 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 97
  (Polychromatic418967fa.accept_10_1_6_7_1_710 1 36 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 97)))))))))))))))))))))))))))))))))))) (allB_succ 35 97 (allA_of_3_1 35 35 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 97 (allA_succ_of_accept 33 34 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 97 (accept_3_3 32 34 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 34 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 97
  (Polychromatic418967fa.accept_19_11_15_2_1_4096 30 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 34 97 (accept_3_3 29 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34
  97 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 34 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 97 (accept_3_3 26 34 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 34 97 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 34 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 97 (Polychromatic418967fa.accept_13_11_8_6_1_1023
  24 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 97 (accept_3_3 23 34
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 97 (Polychromatic418967fa.accept_10_2_4_7_1_352
  22 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 97 (accept_3_3 20 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 34
  97 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 34 97 (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 34 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 97 (accept_3_3 17 34 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 34 97 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 34 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 34 97 (accept_3_3 14 34 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 34 97 (Polychromatic418967fa.accept_10_3_4_7_1_353 13
  34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 34 97
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 34 97 (accept_3_3 11 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34
  97 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 34 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 34 97 (accept_3_3 8 34 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 34 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 34 97 (Polychromatic418967fa.accept_16_6_2_1_1_4081 6
  34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 97 (accept_3_3 5 34 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 97 (Polychromatic418967fa.accept_12_4_10_1_1_706 4
  34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 97 (accept_3_3 2 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 97
  (Polychromatic418967fa.accept_10_1_4_7_1_374 1 34 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 97)))))))))))))))))))))))))))))))))) (allB_succ 33 97 (allA_succ_of_accept 32 33 97 (accept_3_3 32 33 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 31
  33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 97
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 97 (accept_3_3 29 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 33 97 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 33 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 97 (accept_3_3 26 33 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 33 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 33 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 97 (Polychromatic418967fa.accept_10_4_3_7_1_1110
  24 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 97 (accept_3_3 23 33
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 97 (Polychromatic418967fa.accept_6_4_3_1_1_57
  22 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 97
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 97 (accept_3_3 20 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33
  97 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 33 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 97 (accept_3_3 17 33 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 33 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 97 (accept_3_3 14 33 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 13
  33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 97
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 97 (accept_3_3 11 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 33 97 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 33 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 97 (accept_3_3 8 33 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 33 97 (Polychromatic418967fa.accept_19_7_14_2_1_4095 7 33 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 97 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6
  33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 97 (accept_3_3 5 33 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 97
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 97 (accept_3_3 2 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 97
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 33 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 97))))))))))))))))))))))))))))))))) (allB_succ 32 97 (allA_of_3_1 32 32 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 31 97 (allA_succ_of_accept 30 31 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 97 (accept_3_3 29 31 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 97
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 97 (accept_3_3 26 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31
  97 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 97 (accept_3_3 23 31 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 97 (Polychromatic418967fa.accept_9_3_4_7_1_89 21
  31 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 97 (accept_3_3 20 31 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 97 (accept_3_3 17 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 31
  97 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 31 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 31 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 97 (accept_3_3 14 31 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 31 97 (Polychromatic418967fa.accept_23_13_8_5_1_4094 13 31 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 97 (Polychromatic418967fa.accept_9_3_4_7_1_89 12
  31 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 97 (accept_3_3 11 31 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 97
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 97 (accept_3_3 8 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 97
  (Polychromatic418967fa.accept_21_7_10_13_1_4093 7 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 97 (accept_3_3 5 31 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 31 97 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 31 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 97 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 31 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 97 (accept_3_3 2 31 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 97 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 31 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 97))))))))))))))))))))))))))))))) (allB_succ
  30 97 (allA_succ_of_accept 29 30 97 (accept_3_3 29 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 30 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 97 (accept_3_3 26 30 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 30 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 97
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 97 (accept_3_3 23 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30
  97 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 30 97 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 30 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 97 (accept_3_3 20 30 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 30 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 18
  30 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 97 (accept_3_3 17 30 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 97
  (Polychromatic418967fa.accept_17_16_13_12_1_4092 16 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 30 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 97 (accept_3_3 14 30 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 30 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 30 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 97 (Polychromatic418967fa.accept_21_12_9_13_1_4091
  12 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 97 (accept_3_3 11 30
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 97 (Polychromatic418967fa.accept_7_3_2_6_1_56
  10 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 97
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 97 (accept_3_3 8 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 30 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 30 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 97 (accept_3_3 5 30 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 30 97 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 30 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 97 (accept_3_3 2 30 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 30
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 97))))))))))))))))))))))))))))))
  (allB_succ 29 97 (allA_of_3_1 29 29 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 97 (allA_succ_of_accept
  27 28 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 28 97 (accept_3_3 26 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 28 97 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 28 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 28 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 97 (accept_3_3 23 28 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 22
  28 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 97 (accept_3_3 20 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 28
  97 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 28 97 (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 28 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 97 (accept_3_3 17 28 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 28 97 (Polychromatic418967fa.accept_17_16_11_12_1_2008 16 28 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 97 (accept_3_3 14 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 28
  97 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 28 97 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 28 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 97 (accept_3_3 11 28 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 28 97 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 97 (accept_3_3 8 28 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 97 (Polychromatic418967fa.accept_19_7_9_2_1_4090 7
  28 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 97
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 97 (accept_3_3 5 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 97
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 97 (accept_3_3 2 28 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 28 97 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 28 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 97)))))))))))))))))))))))))))) (allB_succ 27 97 (allA_succ_of_accept 26
  27 97 (accept_3_3 26 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 97
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 25 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 97 (Polychromatic418967fa.accept_18_6_9_7_1_2905 24 27 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 97 (accept_3_3 23 27 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 27 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 97 (Polychromatic418967fa.accept_12_9_3_1_1_303 21
  27 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 97 (accept_3_3 20 27 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 97 (Polychromatic418967fa.accept_15_4_12_7_1_3115
  19 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 97 (accept_3_3 17 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 27 97 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 27 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 97 (accept_3_3 14 27 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 27 97 (Polychromatic418967fa.accept_19_13_8_2_1_4089 13 27 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 97 (Polychromatic418967fa.accept_16_12_11_1_1_4088
  12 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 97 (accept_3_3 11 27
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  27 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 97
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 97 (accept_3_3 8 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 97
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 97 (accept_3_3 5 27 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 97 (Polychromatic418967fa.accept_13_3_1_6_1_509 3 27 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 97 (accept_3_3 2 27 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 97 (Polychromatic418967fa.accept_19_1_8_2_1_2876 1 27 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 97))))))))))))))))))))))))))) (allB_succ 26
  97 (allA_of_3_1 26 26 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 97 (allA_succ_of_accept 24 25 97
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 97 (accept_3_3 23 25 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25
  97 (Polychromatic418967fa.accept_10_2_5_7_1_1124 22 25 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 25 97 (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 25 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 97 (accept_3_3 20 25 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 25 97 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 25 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 97 (Polychromatic418967fa.accept_10_8_5_7_1_358 18
  25 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 97 (accept_3_3 17 25 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 16
  25 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 97
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 25 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 97 (accept_3_3 14 25 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25
  97 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 25 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 25 97 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 97 (accept_3_3 11 25 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 25 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 25 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 25
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 97 (accept_3_3 8 25 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 97 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7
  25 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 97
  (Polychromatic418967fa.accept_11_6_3_9_1_906 6 25 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 97 (accept_3_3 5 25 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 97
  (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 25 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 25 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 97 (accept_3_3 2 25 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 97 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 25 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 97))))))))))))))))))))))))) (allB_succ 24 97
  (allA_succ_of_accept 23 24 97 (accept_3_3 23 24 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24
  97 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 24 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 24 97 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 97 (accept_3_3 20 24 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 24 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 97 (Polychromatic418967fa.accept_7_4_3_6_1_340 18
  24 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 97 (accept_3_3 17 24 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 97 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 24
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 97
  (Polychromatic418967fa.accept_11_4_2_9_1_496 15 24 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 97 (accept_3_3 14 24 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24
  97 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 24 97 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 24 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 97 (accept_3_3 11 24 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 24 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 24 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 97 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 97 (accept_3_3 8 24 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 97 (Polychromatic418967fa.accept_11_7_2_9_1_480 7
  24 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 97
  (Polychromatic418967fa.accept_21_6_3_13_1_2742 6 24 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 97 (accept_3_3 5 24 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 97
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 24 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 97 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 97 (accept_3_3 2 24 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 97)))))))))))))))))))))))) (allB_succ 23 97 (allA_of_3_1 23 23
  97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 97 (allA_succ_of_accept 21 22 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 97 (accept_3_3 20 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22
  97 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 22 97 (Polychromatic418967fa.accept_16_2_6_1_1_2069 18 22 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 97 (accept_3_3 17 22 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 22 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 22 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  22 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 97 (accept_3_3 14 22 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 97 (Polychromatic418967fa.accept_18_13_4_7_1_4086
  13 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 97
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 22 97 (accept_3_3 11 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 22 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 97 (accept_3_3 8 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 22 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 22 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 97 (accept_3_3 5 22 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 97 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 22 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 97 (accept_3_3 2 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 97
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 97)))))))))))))))))))))) (allB_succ 21 97 (allA_succ_of_accept 20 21 97 (accept_3_3 20 21 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 21 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 97
  (Polychromatic418967fa.accept_20_18_1_17_1_4085 18 21 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 97 (accept_3_3 17 21 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21
  97 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 21 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 21 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 97 (accept_3_3 14 21 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 21 97 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 21 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 97 (Polychromatic418967fa.accept_8_4_5_1_1_299 12
  21 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 97 (accept_3_3 11 21 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  21 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 97
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 21 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 97 (accept_3_3 8 21 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 97
  (Polychromatic418967fa.accept_17_7_4_12_1_4084 7 21 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 97 (accept_3_3 5 21 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 97 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  21 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 97 (accept_3_3 2 21 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 21
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 97))))))))))))))))))))) (allB_succ 20 97
  (allA_of_3_1 20 20 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 97 (allA_succ_of_accept 18 19 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 97 (accept_3_3 17 19 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19
  97 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 19 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 19 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 97 (accept_3_3 14 19 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 97 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 19 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 97
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 97 (accept_3_3 11 19 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19
  97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 19 97 (Polychromatic418967fa.accept_23_9_19_5_1_4082 9 19 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 97 (accept_3_3 8 19 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 19 97 (Polychromatic418967fa.accept_17_7_2_12_1_1069 7 19 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 97 (accept_3_3 5 19 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 19
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 97
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 19 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 97 (accept_3_3 2 19 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 97
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 19 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 19 97))))))))))))))))))) (allB_succ 18 97 (allA_succ_of_accept 17 18 97 (accept_3_3 17 18 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 18 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 18 97 (accept_3_3 14 18 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18
  97 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 18 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 18 97 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 18 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 97 (accept_3_3 11 18 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 18 97 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 18 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 97 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 97 (accept_3_3 8 18 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 97
  (Polychromatic418967fa.accept_16_6_2_1_1_4081 6 18 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 97 (accept_3_3 5 18 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 97
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 4 18 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 18 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 97 (accept_3_3 2 18 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 18 97 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 18 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 97)))))))))))))))))) (allB_succ 17 97 (allA_of_3_1 17 17 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 97 (allA_succ_of_accept 15 16 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 97 (accept_3_3 14 16 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16
  97 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 16 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 16 97 (Polychromatic418967fa.accept_23_12_16_5_1_4080 12 16 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 97 (accept_3_3 11 16 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 16 97 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 16 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 97 (accept_3_3 8 16 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 97 (Polychromatic418967fa.accept_11_7_5_9_1_884 7
  16 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 97
  (Polychromatic418967fa.accept_15_6_1_7_1_4079 6 16 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 97 (accept_3_3 5 16 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 97
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 16 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 97 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 97 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 97 (accept_3_3 2 16 97 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 16 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 16 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 97)))))))))))))))) (allB_succ 15 97 (allA_succ_of_accept 14 15 97
  (accept_3_3 14 15 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 97
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 15 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 97 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 97 (accept_3_3 11 15 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 97 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 97 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 15
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 97 (accept_3_3 8 15 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 97 (Polychromatic418967fa.accept_14_7_1_13_1_357 7
  15 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 97
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 97 (accept_3_3 5 15 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 97
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 97 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 15 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 97 (accept_3_3 2 15 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 15 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 97))))))))))))))) (allB_succ 14 97 (allA_of_3_1 14 14 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 97 (allA_succ_of_accept 12 13 97
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 13 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 97 (accept_3_3 11 13 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  97 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 13 97 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 13 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 97 (accept_3_3 8 13 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 97 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 13 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 97 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 97 (accept_3_3 5 13 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 97 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 13
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 97
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 13 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 97 (accept_3_3 2 13 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 97
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 97))))))))))))) (allB_succ 12 97 (allA_succ_of_accept 11 12 97 (accept_3_3 11 12 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 12 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 97
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 12 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 12 97 (accept_3_3 8 12 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 97
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 12 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 12 97 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 12 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 97 (accept_3_3 5 12 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 12 97 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 12 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 97 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3
  12 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 97 (accept_3_3 2 12 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 97 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 97)))))))))))) (allB_succ 11 97
  (allA_of_3_1 11 11 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 97 (allA_succ_of_accept 9 10 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 97 (accept_3_3 8 10 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 97
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 97 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 10 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 97 (accept_3_3 5 10 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 97 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 10 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 97 (accept_3_3 2 10 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 97 (Polychromatic418967fa.accept_11_1_10_9_1_871 1
  10 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 97)))))))))) (allB_succ 9 97
  (allA_succ_of_accept 8 9 97 (accept_3_3 8 9 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 97
  (Polychromatic418967fa.accept_13_7_9_6_1_148 7 9 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 97 (Polychromatic418967fa.accept_18_6_9_7_1_2905 6 9 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 97 (accept_3_3 5 9 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 97 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 97 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 97 (accept_3_3 2 9 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 97 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 9 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 97))))))))) (allB_succ 8 97 (allA_of_3_1 8 8 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 97 (allA_succ_of_accept 6 7 97 (Polychromatic418967fa.accept_4_2_3_1_1_2
  6 7 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 97 (accept_3_3 5 7 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 97 (Polychromatic418967fa.accept_13_4_7_6_1_2359 4 7
  97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 97
  (Polychromatic418967fa.accept_17_3_7_12_1_2016 3 7 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 7 97 (accept_3_3 2 7 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 97
  (Polychromatic418967fa.accept_13_1_7_6_1_142 1 7 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 7 97))))))) (allB_succ 6 97 (allA_succ_of_accept 5 6 97 (accept_3_3 5 6 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 6 97 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 6 97 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 97 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 97 (accept_3_3 2 6 97 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 97 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 97
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 97)))))) (allB_succ 5 97 (allA_of_3_1 5 5 97
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 4 97 (allA_succ_of_accept 3 4 97
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 97 (accept_3_3 2 4 97 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 97
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 97 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 97)))) (allB_succ 3 97 (allA_succ_of_accept 2 3 97 (accept_3_3 2 3 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 97 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 3 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 97))) (allB_succ 2 97 (allA_of_3_1 2 2 97 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_two
  97)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


