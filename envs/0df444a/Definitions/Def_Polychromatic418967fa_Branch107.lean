-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch107
-- name    : Polychromatic418967fa_Branch107
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:10:36.318363+00:00
-- url     : https://prove2.me/theorems/2e9b1320-0615-4508-97bf-e8576061ed7d
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

def Polychromatic418967fa.branch_107 : allB 107 107 :=
  allB_succ' 2 106 107 (Eq.refl Bool.true) (allA_of_3_0 2 106 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  105 107 (Eq.refl Bool.true) (allA_succ_of_accept 2 105 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 107 (accept_3_2 1 105 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 107))) (allB_succ' 4 104 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 104 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 104 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 107 (accept_3_2 1 104 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104 107)))) (allB_succ' 5 103 107 (Eq.refl Bool.true) (allA_of_3_0
  5 103 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 102 107 (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 102 107 (accept_3_2 4 102 107 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 102 107 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 102 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 102 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 107 (accept_3_2 1 102 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 107)))))) (allB_succ' 7 101 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 101 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 107 (accept_3_2 4 101 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  101 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 107 (accept_3_2 1 101 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101 107)))))))
  (allB_succ' 8 100 107 (Eq.refl Bool.true) (allA_of_3_0 8 100 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 99 107 (Eq.refl Bool.true) (allA_succ_of_accept 8 99 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 107 (accept_3_2 7 99 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  99 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 107
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 99 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 107 (accept_3_2 4 99 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  107 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 107 (accept_3_2 1 99 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 107))))))))) (allB_succ' 10 98 107 (Eq.refl Bool.true) (allA_succ_of_accept 9 98 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 98 107 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 98 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 98 107 (accept_3_2 7 98 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 98 107 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 98 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 98 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 107 (accept_3_2 4 98 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 107
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 2 98 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 107 (accept_3_2 1 98 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 107))))))))))
  (allB_succ' 11 97 107 (Eq.refl Bool.true) (allA_of_3_0 11 97 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  12 96 107 (Eq.refl Bool.true) (allA_succ_of_accept 11 96 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 107 (accept_3_2 10 96 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 107 (Polychromatic418967fa.accept_13_9_5_3_1_428 9
  96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 107
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 107 (accept_3_2 7 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96
  107 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 107 (accept_3_2 4 96 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 96 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 107 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 107 (accept_3_2 1 96 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 107)))))))))))) (allB_succ' 13 95 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 95 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 107 (accept_3_2 10 95 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 107 (Polychromatic418967fa.accept_21_9_11_2_1_238 9
  95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 107
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 107 (accept_3_2 7 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  107 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 95 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 107 (accept_3_2 4 95 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 95 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 95
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 107 (accept_3_2 1 95 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 107))))))))))))) (allB_succ' 14 94 107 (Eq.refl Bool.true)
  (allA_of_3_0 14 94 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 93 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 14 93 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 107 (accept_3_2 13 93 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 107 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 93 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 107
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 107 (accept_3_2 10 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 107 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 107 (accept_3_2 7 93 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 107 (accept_3_2 4 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  107 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 107 (accept_3_2 1 93 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93 107))))))))))))))) (allB_succ' 16 92 107 (Eq.refl Bool.true) (allA_succ_of_accept 15 92 107
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 92 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 92 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 92 107 (accept_3_2 13 92 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 92 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 92 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 92 107 (Polychromatic418967fa.accept_13_11_1_3_1_910
  11 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 107 (accept_3_2 10
  92 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 107
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 92 107 (Polychromatic418967fa.accept_16_8_12_11_1_3697 8 92 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 92 107 (accept_3_2 7 92 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 92 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 92 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 92 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 107 (accept_3_2 4 92 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 92 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 107
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 92 107 (accept_3_2 1 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  107)))))))))))))))) (allB_succ' 17 91 107 (Eq.refl Bool.true) (allA_of_3_0 17 91 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 90 107 (Eq.refl Bool.true) (allA_succ_of_accept 17 90 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 107 (accept_3_2 16 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 107 (Polychromatic418967fa.accept_21_14_6_2_1_4793 14 90 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 107 (accept_3_2 13 90 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 107 (Polychromatic418967fa.accept_16_12_10_11_1_2667 12 90
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 107
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 107 (accept_3_2 10 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 90 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 107 (accept_3_2 7 90 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 90 107 (Polychromatic418967fa.accept_19_6_14_12_1_4811 6 90 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 107 (accept_3_2 4 90 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 90
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 107
  (Polychromatic418967fa.accept_13_2_12_3_1_415 2 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 107 (accept_3_2 1 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  107)))))))))))))))))) (allB_succ' 19 89 107 (Eq.refl Bool.true) (allA_succ_of_accept 18 89 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 89 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 107 (accept_3_2 16 89 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 89 107 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 89 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 107 (accept_3_2 13 89
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 107
  (Polychromatic418967fa.accept_10_2_9_7_1_720 12 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 89 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 89 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 107 (accept_3_2 10 89 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 89 107 (Polychromatic418967fa.accept_24_9_17_11_1_4810 9 89 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 107 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8
  89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 107 (accept_3_2 7 89 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 107
  (Polychromatic418967fa.accept_13_5_11_3_1_902 5 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 107 (accept_3_2 4 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  107 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 107 (accept_3_2 1 89 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 107))))))))))))))))))) (allB_succ' 20 88 107 (Eq.refl Bool.true) (allA_of_3_0 20 88 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 87 107 (Eq.refl Bool.true) (allA_succ_of_accept 20 87 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 107 (accept_3_2 19 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 107 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 107 (Polychromatic418967fa.accept_21_17_3_2_1_2111 17 87 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 107 (accept_3_2 16 87 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 107 (accept_3_2 13 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 107 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 87 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 107 (accept_3_2 10 87 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 107 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 87 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 107 (accept_3_2 7 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  107 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 87 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 107 (accept_3_2 4 87 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 107 (accept_3_2 1 87 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 107))))))))))))))))))))) (allB_succ' 22 86 107 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 86 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 86 107 (accept_3_2 19 86
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 86 107
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 86 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 107 (accept_3_2 16 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 86 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 107
  (Polychromatic418967fa.accept_19_14_10_12_1_4809 14 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 86 107 (accept_3_2 13 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 86 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 86 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 107 (accept_3_2 10 86 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 107
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 107 (accept_3_2 7 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  107 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 107 (accept_3_2 4 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 86
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 107 (accept_3_2 1 86 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86 107)))))))))))))))))))))) (allB_succ' 23 85 107 (Eq.refl
  Bool.true) (allA_of_3_0 23 85 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 84 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 107 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 107 (accept_3_2 22 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 107 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 84 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 20
  84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 107 (accept_3_2 19 84
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 107
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 107 (Polychromatic418967fa.accept_20_17_4_7_1_4808 17 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 107 (accept_3_2 16 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 107 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 107 (Polychromatic418967fa.accept_9_5_3_8_1_316 14
  84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 107 (accept_3_2 13 84
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 107
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 107 (accept_3_2 10 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 107 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 84 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 107 (Polychromatic418967fa.accept_15_8_9_2_1_1897 8
  84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 107 (accept_3_2 7 84 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 6
  84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 107 (accept_3_2 4 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  107 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 107 (accept_3_2 1 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 107)))))))))))))))))))))))) (allB_succ' 25 83 107 (Eq.refl Bool.true) (allA_succ_of_accept 24
  83 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 83 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 107 (accept_3_2 22 83 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 83 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 107
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 20 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 107 (accept_3_2 19 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 83 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 107 (accept_3_2 16 83 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 83 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 107 (accept_3_2 13 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 107 (accept_3_2 10 83 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 107 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 83 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 107
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 107 (accept_3_2 7 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  107 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 107 (accept_3_2 4 83 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 83 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 107 (Polychromatic418967fa.accept_13_2_5_3_1_406 2
  83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 107 (accept_3_2 1 83 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83 107))))))))))))))))))))))))) (allB_succ' 26 82 107 (Eq.refl
  Bool.true) (allA_of_3_0 26 82 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 81 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 107 (accept_3_2 25 81 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 107 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 107 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  23 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 107 (accept_3_2 22
  81 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 107
  (Polychromatic418967fa.accept_25_21_6_7_1_4807 21 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 107 (accept_3_2 19 81 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 107
  (Polychromatic418967fa.accept_19_17_5_12_1_4753 17 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 107 (accept_3_2 16 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 107 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 107 (accept_3_2 13 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 107
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 11 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 107 (accept_3_2 10 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 107 (Polychromatic418967fa.accept_17_9_13_5_1_3512 9 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 107 (accept_3_2 7 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 107
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 107 (accept_3_2 4 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  107 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 81 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 107 (accept_3_2 1 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 81 107))))))))))))))))))))))))))) (allB_succ' 28 80 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 80 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 80 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 80 107 (accept_3_2 25 80 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 80 107 (Polychromatic418967fa.accept_13_11_2_3_1_883
  24 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 107
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 80 107 (accept_3_2 22 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  80 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 80 107 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 80 107 (accept_3_2 19 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 107 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 80 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 107
  (Polychromatic418967fa.accept_11_6_3_8_1_843 17 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 80 107 (accept_3_2 16 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  80 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 80 107 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 107 (accept_3_2 13 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 80 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 107
  (Polychromatic418967fa.accept_13_11_2_3_1_883 11 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 80 107 (accept_3_2 10 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  80 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 80 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 107 (accept_3_2 7 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 107 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 80 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 80 107
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 80 107 (accept_3_2 4 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80
  107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 80 107 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 80 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 107 (accept_3_2 1 80 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 107)))))))))))))))))))))))))))) (allB_succ' 29 79 107 (Eq.refl Bool.true) (allA_of_3_0 29 79
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 78 107 (Eq.refl Bool.true) (allA_succ_of_accept 29 78 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 107 (accept_3_2 28 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 107 (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 78 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 107 (accept_3_2 25 78 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 107 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 78 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 107
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 107 (accept_3_2 22 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 78 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 107 (accept_3_2 19 78 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 107 (Polychromatic418967fa.accept_21_18_15_2_1_4806 18 78 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 107 (accept_3_2 16 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 107 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 78 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 107 (accept_3_2 13 78 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 78 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 107
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 107 (accept_3_2 10 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 107 (Polychromatic418967fa.accept_21_8_15_2_1_4805 8 78 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 107 (accept_3_2 7 78 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 78 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 107 (accept_3_2 4 78 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 107 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 107
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 107 (accept_3_2 1 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  107)))))))))))))))))))))))))))))) (allB_succ' 31 77 107 (Eq.refl Bool.true) (allA_succ_of_accept 30 77 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 77 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 107 (accept_3_2 28 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 77 107 (Polychromatic418967fa.accept_19_8_1_12_1_4804 27 77 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 107 (accept_3_2 25 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 107 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 107 (Polychromatic418967fa.accept_19_4_1_12_1_4803 23 77 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 107 (accept_3_2 22 77 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 77 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 107
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 107 (accept_3_2 19 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 107 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 77 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 107 (accept_3_2 16 77 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 107 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 77 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 107 (accept_3_2 13 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 107 (accept_3_2 10 77 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 107 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 77 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 107
  (Polychromatic418967fa.accept_16_8_13_11_1_4772 8 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 107 (accept_3_2 7 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 107 (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 107 (accept_3_2 4 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 77 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 107 (accept_3_2 1 77 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 107))))))))))))))))))))))))))))))) (allB_succ' 32 76 107
  (Eq.refl Bool.true) (allA_of_3_0 32 76 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 75 107 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 75 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 107 (accept_3_2 31 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 107 (Polychromatic418967fa.accept_19_11_18_12_1_4802 30 75 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 107
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 107 (accept_3_2 28 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  75 107 (Polychromatic418967fa.accept_21_6_12_2_1_4801 27 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 75 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 107 (accept_3_2 25 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 107 (accept_3_2 22 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  75 107 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 75 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 107 (accept_3_2 19 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 107
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 107 (accept_3_2 16 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  75 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 75 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 107 (accept_3_2 13 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 107 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 75 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 107
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 107 (accept_3_2 10 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  75 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 107 (accept_3_2 7 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 75 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 107 (accept_3_2 4 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  107 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 107 (accept_3_2 1 75 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 75 107))))))))))))))))))))))))))))))))) (allB_succ' 34 74 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 74 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 74 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 107 (accept_3_2 31 74 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 30
  74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 74 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 74 107 (accept_3_2 28 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  74 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 74 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 74 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 107 (accept_3_2 25 74 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 74 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 74 107 (accept_3_2 22 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  74 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 74 107 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 74 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 107 (accept_3_2 19 74 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 107 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 74 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 74 107 (accept_3_2 16 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  74 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 74 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 74 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 107 (accept_3_2 13 74 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 74 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 107
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 74 107 (accept_3_2 10 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  74 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 74 107 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 107 (accept_3_2 7 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 74 107 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 74 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 107 (accept_3_2 4 74 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 107
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 74 107 (accept_3_2 1 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  107)))))))))))))))))))))))))))))))))) (allB_succ' 35 73 107 (Eq.refl Bool.true) (allA_of_3_0 35 73 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 72 107 (Eq.refl Bool.true) (allA_succ_of_accept 35 72 107
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 107 (accept_3_2 34 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 107 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 107 (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 107 (accept_3_2 31 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 107 (Polychromatic418967fa.accept_13_4_7_3_1_92 30 72 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 107
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 107 (accept_3_2 28 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 107 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 107 (Polychromatic418967fa.accept_19_7_15_12_1_4800 26 72 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 107 (accept_3_2 25 72 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 107 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 72 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 107
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 107 (accept_3_2 22 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 107 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 107 (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 72 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 107 (accept_3_2 19 72 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 107 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 72 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 107
  (Polychromatic418967fa.accept_13_4_7_3_1_92 17 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 107 (accept_3_2 16 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 107 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 107 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 107 (accept_3_2 13 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 107 (Polychromatic418967fa.accept_16_12_8_11_1_2695 12 72 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 107
  (Polychromatic418967fa.accept_13_11_7_3_1_894 11 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 107 (accept_3_2 10 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 107 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 107 (Polychromatic418967fa.accept_13_8_7_3_1_430 8 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 107 (accept_3_2 7 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 107 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 72 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 107
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 107 (accept_3_2 4 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  107 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 72 107 (Polychromatic418967fa.accept_20_2_12_7_1_4799 2 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 107 (accept_3_2 1 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 107)))))))))))))))))))))))))))))))))))) (allB_succ' 37 71 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 71 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 107 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 71 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 107 (accept_3_2 34 71 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 107
  (Polychromatic418967fa.accept_23_10_2_15_1_4798 33 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 71 107 (Polychromatic418967fa.accept_19_13_14_12_1_4797 32 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 107 (accept_3_2 31 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 71 107 (Polychromatic418967fa.accept_20_10_11_7_1_4796 30 71 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 107
  (Polychromatic418967fa.accept_19_10_14_12_1_4795 29 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 71 107 (accept_3_2 28 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 71 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 107 (Polychromatic418967fa.accept_10_6_1_7_1_342 26 71 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 107 (accept_3_2 25 71 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 107 (Polychromatic418967fa.accept_7_3_1_2_1_247 24
  71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 107
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 107 (accept_3_2 22 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 107 (Polychromatic418967fa.accept_15_6_11_2_1_2801 21 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 107 (accept_3_2 19 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 107 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 71 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 107
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 107 (accept_3_2 16 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 107 (Polychromatic418967fa.accept_16_15_7_11_1_3760 15 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 107 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 107 (accept_3_2 13 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 71 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 107
  (Polychromatic418967fa.accept_25_11_21_7_1_4794 11 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 107 (accept_3_2 10 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 107 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 107 (Polychromatic418967fa.accept_14_8_1_9_1_2085 8 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 107 (accept_3_2 7 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 71 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 107
  (Polychromatic418967fa.accept_13_5_6_3_1_868 5 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 107 (accept_3_2 4 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  107 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 107 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 107 (accept_3_2 1 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 107))))))))))))))))))))))))))))))))))))) (allB_succ' 38 70 107 (Eq.refl Bool.true)
  (allA_of_3_0 38 70 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 69 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 69 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 107 (accept_3_2 37 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 107 (Polychromatic418967fa.accept_21_14_6_2_1_4793
  35 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 107 (accept_3_2 34
  69 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 107
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 107 (accept_3_2 31 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 107 (accept_3_2 28 69
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 107
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 107 (accept_3_2 25 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 23
  69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 107 (accept_3_2 22 69
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 107
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 107 (accept_3_2 19 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 107 (accept_3_2 16 69
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 107 (Polychromatic418967fa.accept_7_1_6_2_1_18
  15 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 107 (accept_3_2 13 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 107 (accept_3_2 10 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 107 (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 69 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 107 (accept_3_2 7 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 107 (accept_3_2 4 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 107 (accept_3_2 1 69 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 107))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 68 107
  (Eq.refl Bool.true) (allA_succ_of_accept 39 68 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 107
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 107 (accept_3_2 37 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 107 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 107 (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 107 (accept_3_2 34 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 107
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 107 (accept_3_2 31 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 107 (accept_3_2 28 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 107
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 107 (accept_3_2 25 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 107 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 107 (accept_3_2 22 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 107
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 107 (accept_3_2 19 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 107 (accept_3_2 16 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 107
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 107 (accept_3_2 13 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 107 (accept_3_2 10 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 107
  (Polychromatic418967fa.accept_16_8_4_11_1_2687 8 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 107 (accept_3_2 7 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  107 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 107 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 107 (accept_3_2 4 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 68
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 107 (accept_3_2 1 68 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 107)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 67
  107 (Eq.refl Bool.true) (allA_of_3_0 41 67 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 66 107 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 107 (accept_3_2 40 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 107 (Polychromatic418967fa.accept_16_7_2_11_1_931 39 66 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 107
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 107 (accept_3_2 37 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  66 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 66 107 (Polychromatic418967fa.accept_19_16_9_12_1_4792 35 66 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 107 (accept_3_2 34 66 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 66 107 (accept_3_2 31 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  66 107 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 66 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 107 (accept_3_2 28 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 107 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 107
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 66 107 (accept_3_2 25 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  66 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 66 107 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 107 (accept_3_2 22 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 107
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 107 (accept_3_2 19 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  66 107 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 66 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 107 (accept_3_2 16 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 66 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 66 107 (accept_3_2 13 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  66 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 66 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 107 (accept_3_2 10 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 107
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 66 107 (accept_3_2 7 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66
  107 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 107 (accept_3_2 4 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 66 107 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 107 (accept_3_2 1 66 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 107)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 65
  107 (Eq.refl Bool.true) (allA_succ_of_accept 42 65 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 107 (accept_3_2 40 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 107 (accept_3_2 37 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 107 (Polychromatic418967fa.accept_17_2_14_5_1_2575 36 65 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 107
  (Polychromatic418967fa.accept_20_15_5_7_1_4791 35 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 107 (accept_3_2 34 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 107 (accept_3_2 31 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 107
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 107 (accept_3_2 28 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 107 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 107 (accept_3_2 25 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 107 (accept_3_2 22 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 107 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 107 (accept_3_2 19 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 107
  (Polychromatic418967fa.accept_22_17_21_19_1_4790 17 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 65 107 (accept_3_2 16 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 65 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 107 (accept_3_2 13 65 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 12
  65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 107
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 107 (accept_3_2 10 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 107 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 107 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 107 (accept_3_2 7 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 107 (accept_3_2 4 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  107 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 107 (accept_3_2 1 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 107))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 64 107 (Eq.refl Bool.true)
  (allA_of_3_0 44 64 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 63 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 107 (accept_3_2 43 63 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 107 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 63 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 107
  (Polychromatic418967fa.accept_13_2_11_3_1_873 41 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 107 (accept_3_2 40 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  63 107 (Polychromatic418967fa.accept_16_7_15_11_1_951 39 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 63 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 107 (accept_3_2 37 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 107
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 107 (accept_3_2 34 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  63 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 63 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 107 (accept_3_2 31 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 107 (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 63 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 107
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 29 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 107 (accept_3_2 28 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  63 107 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 63 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 107 (accept_3_2 25 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 107 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 63 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 107
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 107 (accept_3_2 22 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  63 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 63 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 107 (accept_3_2 19 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 107 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 63 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 107
  (Polychromatic418967fa.accept_16_1_15_11_1_356 17 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 107 (accept_3_2 16 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  63 107 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 63 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 107 (accept_3_2 13 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 107
  (Polychromatic418967fa.accept_23_11_17_15_1_4789 11 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 63 107 (accept_3_2 10 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 63 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 107 (accept_3_2 7 63 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 107 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6
  63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 107
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 107 (accept_3_2 4 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63
  107 (Polychromatic418967fa.accept_16_3_15_11_1_2676 3 63 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 63 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 107 (accept_3_2 1 63 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 63 107))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 62 107 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 62 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 107 (Polychromatic418967fa.accept_10_4_2_7_1_373
  44 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 107 (accept_3_2 43
  62 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 107
  (Polychromatic418967fa.accept_19_4_5_12_1_3441 42 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 107 (accept_3_2 40 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 107 (accept_3_2 37 62
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 107 (Polychromatic418967fa.accept_7_1_6_2_1_18
  36 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 107
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 107 (accept_3_2 34 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 107 (accept_3_2 31 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 107 (Polychromatic418967fa.accept_19_11_5_12_1_3439 30 62 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 107 (accept_3_2 28 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 107 (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 107 (accept_3_2 25 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 62 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 107
  (Polychromatic418967fa.accept_17_6_11_5_1_3506 23 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 107 (accept_3_2 22 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 107 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 107 (accept_3_2 19 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 62 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 107 (accept_3_2 16 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 107 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 107 (accept_3_2 13 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 107 (Polychromatic418967fa.accept_20_12_2_7_1_4788 12 62 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 107
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 107 (accept_3_2 10 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 62 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 107 (accept_3_2 7 62 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 62 107 (Polychromatic418967fa.accept_13_6_10_3_1_897 6 62 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 107 (accept_3_2 4 62 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 107
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 62 107 (accept_3_2 1 62 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  107)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 61 107 (Eq.refl Bool.true) (allA_of_3_0 47 61 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 60 107 (Eq.refl Bool.true) (allA_succ_of_accept 47 60 107
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 107 (accept_3_2 46 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 107 (Polychromatic418967fa.accept_19_7_3_12_1_4787 45 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 107 (Polychromatic418967fa.accept_13_5_8_3_1_1535 44 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 107 (accept_3_2 43 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 107 (Polychromatic418967fa.accept_16_10_12_11_1_346 42 60 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 107
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 107 (accept_3_2 40 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 107 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 107 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 107 (accept_3_2 37 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 107 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 60 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 107
  (Polychromatic418967fa.accept_11_2_5_8_1_470 35 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 107 (accept_3_2 34 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 107 (accept_3_2 31 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 60 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 107
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 107 (accept_3_2 28 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 107 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 107 (accept_3_2 25 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 107 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 60 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 107
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 107 (accept_3_2 22 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 107 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 107 (accept_3_2 19 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 107 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 60 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 107
  (Polychromatic418967fa.accept_16_1_12_11_1_2648 17 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 107 (accept_3_2 16 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 107 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 107 (accept_3_2 13 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 60 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 107
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 107 (accept_3_2 10 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 107 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 107 (Polychromatic418967fa.accept_16_8_12_11_1_3697 8 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 107 (accept_3_2 7 60 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 107 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 60 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 107
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 107 (accept_3_2 4 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  107 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 107 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 107 (accept_3_2 1 60 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 107)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 59 107 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 59 107 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 107 (accept_3_2 46 59 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 107 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  45 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 107
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 107 (accept_3_2 43 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 107 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 107 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 107 (accept_3_2 40 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 59 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 107
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 107 (accept_3_2 37 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 107 (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 107 (accept_3_2 34 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 59 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 107
  (Polychromatic418967fa.accept_10_2_9_7_1_720 32 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 107 (accept_3_2 31 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 107 (accept_3_2 28 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 107 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 59 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 107
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 107 (accept_3_2 25 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 107 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 107 (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 107 (accept_3_2 22 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 59 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 107
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 107 (accept_3_2 19 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 107 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 107 (Polychromatic418967fa.accept_13_4_7_3_1_92 17 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 107 (accept_3_2 16 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 59 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 107
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 107 (accept_3_2 13 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 107 (accept_3_2 10 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 107 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 59 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 107
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 107 (accept_3_2 7 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  107 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 107 (accept_3_2 4 59 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 59 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 59
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 107 (accept_3_2 1 59 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 107))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  50 58 107 (Eq.refl Bool.true) (allA_of_3_0 50 58 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 57 107
  (Eq.refl Bool.true) (allA_succ_of_accept 50 57 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 107 (accept_3_2 49 57 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 107
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 107 (accept_3_2 46 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  57 107 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 57 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 107 (accept_3_2 43 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 107
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 107 (accept_3_2 40 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  57 107 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 57 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 107 (accept_3_2 37 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 107 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 57 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 107
  (Polychromatic418967fa.accept_13_9_5_3_1_428 35 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 107 (accept_3_2 34 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  57 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 57 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 107 (accept_3_2 31 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 107
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 107 (accept_3_2 28 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  57 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 57 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 107 (accept_3_2 25 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 107 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 107 (accept_3_2 22 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  57 107 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 57 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 107 (accept_3_2 19 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 107
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 107 (accept_3_2 16 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  57 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 57 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 107 (accept_3_2 13 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 107 (Polychromatic418967fa.accept_20_12_17_7_1_4786 12 57 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 107
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 107 (accept_3_2 10 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  57 107 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 57 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 107 (accept_3_2 7 57 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 107 (accept_3_2 4 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57
  107 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 107 (accept_3_2 1 57 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 57 107))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 56 107 (Eq.refl
  Bool.true) (allA_succ_of_accept 51 56 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 50
  56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 56 107 (accept_3_2 49 56
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 56 107
  (Polychromatic418967fa.accept_9_3_2_8_1_108 48 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 56 107 (Polychromatic418967fa.accept_18_11_2_17_1_3490 47 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 107 (accept_3_2 46 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 56 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 107
  (Polychromatic418967fa.accept_16_12_8_11_1_2695 44 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 107 (accept_3_2 43 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 107 (accept_3_2 40 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 107
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 107 (accept_3_2 37 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 107 (Polychromatic418967fa.accept_15_6_11_2_1_2801 36 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 107 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 56 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 107 (accept_3_2 34 56 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 107 (accept_3_2 31 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 107 (Polychromatic418967fa.accept_16_13_8_11_1_4785 29 56 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 107 (accept_3_2 28 56 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 107
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 107 (accept_3_2 25 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 107 (accept_3_2 22 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 107
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 20 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 107 (accept_3_2 19 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 107 (Polychromatic418967fa.accept_23_18_10_15_1_4784 18 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 107 (Polychromatic418967fa.accept_19_17_18_12_1_4783 17 56 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 107 (accept_3_2 16 56 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 107 (accept_3_2 13 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 107 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 107 (accept_3_2 10 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 107
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 8 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 107 (accept_3_2 7 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  107 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 107 (accept_3_2 4 56 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 107 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  56 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 107 (accept_3_2 1 56 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 107))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 55 107 (Eq.refl Bool.true) (allA_of_3_0 53 55 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  54 107 (allA_succ_of_accept 53 54 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 107 (accept_3_2 52 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 107 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 107 (Polychromatic418967fa.accept_13_11_2_3_1_883
  50 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 107 (accept_3_2 49
  54 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 107
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 107 (Polychromatic418967fa.accept_19_9_16_12_1_4760 47 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 107 (accept_3_2 46 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 107 (Polychromatic418967fa.accept_13_5_2_3_1_1526
  44 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 107 (accept_3_2 43
  54 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 107
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 107 (accept_3_2 40 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 107 (accept_3_2 37 54
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 107
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 107 (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 107 (accept_3_2 34 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 107 (accept_3_2 31 54
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 107
  (Polychromatic418967fa.accept_21_9_12_2_1_4781 30 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 107 (accept_3_2 28 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 107 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 107 (Polychromatic418967fa.accept_15_11_9_2_1_4780
  26 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 107 (accept_3_2 25
  54 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 107
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 107 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 107 (accept_3_2 22 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 107 (Polychromatic418967fa.accept_11_9_10_8_1_444
  20 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 107 (accept_3_2 19
  54 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 107
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 107 (accept_3_2 16 54 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 107 (Polychromatic418967fa.accept_19_15_16_12_1_4779 15 54 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 107
  (Polychromatic418967fa.accept_13_1_2_3_1_911 14 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 107 (accept_3_2 13 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 107 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 107 (accept_3_2 10 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 107
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 107 (accept_3_2 7 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  107 (Polychromatic418967fa.accept_17_6_3_5_1_3657 6 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 54 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 107 (accept_3_2 4 54 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 107
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 107 (accept_3_2 1 54 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  107)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 107 (allA_succ_of_accept 52 53 107 (accept_3_2
  52 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 107
  (Polychromatic418967fa.accept_15_6_8_2_1_104 51 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 107 (accept_3_2 49 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 107 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 107 (accept_3_2 46 53
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 107
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 107 (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 107 (accept_3_2 43 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 107 (Polychromatic418967fa.accept_7_6_4_2_1_236 41
  53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 107 (accept_3_2 40 53
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 107
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 107 (accept_3_2 37 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 107 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 107 (Polychromatic418967fa.accept_10_5_3_7_1_1108
  35 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 107 (accept_3_2 34
  53 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 107
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 53 107 (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 107 (accept_3_2 31 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 53 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 107 (Polychromatic418967fa.accept_25_4_3_7_1_4778
  29 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 107 (accept_3_2 28
  53 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 107
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 53 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 107 (accept_3_2 25 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 53 107 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 107 (Polychromatic418967fa.accept_16_7_5_11_1_4777
  23 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 107 (accept_3_2 22
  53 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 107
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 53 107 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 107 (accept_3_2 19 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 53 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 107 (Polychromatic418967fa.accept_13_4_1_3_1_3058
  17 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 107 (accept_3_2 16
  53 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 107
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 53 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 107 (accept_3_2 13 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 53 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 107 (Polychromatic418967fa.accept_13_11_1_3_1_910
  11 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 107 (accept_3_2 10
  53 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 107
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 53 107 (Polychromatic418967fa.accept_16_8_5_11_1_4776 8 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 107 (accept_3_2 7 53 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 53 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 107 (accept_3_2 4 53 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 107 (Polychromatic418967fa.accept_17_3_2_5_1_2556 3
  53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 53 107 (accept_3_2 1 53 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53
  107))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 107 (allA_of_3_0 52 52 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 51 107 (allA_succ_of_accept 50 51 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 107 (accept_3_2 49 51 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 48
  51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 107
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 51 107 (accept_3_2 46 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  51 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 51 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 107 (accept_3_2 43 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 107 (Polychromatic418967fa.accept_15_12_6_2_1_2760 42 51 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 107
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 107 (accept_3_2 40 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  51 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 51 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 107 (accept_3_2 37 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 107 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 51 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 107
  (Polychromatic418967fa.accept_13_9_12_3_1_907 35 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 107 (accept_3_2 34 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  51 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 51 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 107 (accept_3_2 31 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 107
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 107 (accept_3_2 28 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  51 107 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 51 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 107 (accept_3_2 25 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 107 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 51 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 107
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 107 (accept_3_2 22 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  51 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 51 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 107 (accept_3_2 19 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 107 (Polychromatic418967fa.accept_19_18_13_12_1_4775 18 51 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 107
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 107 (accept_3_2 16 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  51 107 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 51 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 107 (accept_3_2 13 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 107
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 107 (accept_3_2 10 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  51 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 51 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 107 (accept_3_2 7 51 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 107 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 51 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 107
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 107 (accept_3_2 4 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  107 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 51 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 107 (accept_3_2 1 51 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 107))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 107 (allA_succ_of_accept
  49 50 107 (accept_3_2 49 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 107
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 107 (accept_3_2 46 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 107 (Polychromatic418967fa.accept_12_8_2_11_1_246
  44 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 107 (accept_3_2 43
  50 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 107
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 107 (accept_3_2 40 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 107 (Polychromatic418967fa.accept_7_3_1_2_1_247 38
  50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 107 (accept_3_2 37 50
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 107
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 107 (Polychromatic418967fa.accept_17_1_16_5_1_3670 35 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 107 (accept_3_2 34 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 107 (Polychromatic418967fa.accept_12_8_2_11_1_246
  32 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 107 (accept_3_2 31
  50 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 107
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 50 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 107 (accept_3_2 28 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 50 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 107 (Polychromatic418967fa.accept_15_11_5_2_1_520
  26 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 50 107 (accept_3_2 25
  50 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 50 107
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 50 107 (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 107 (accept_3_2 22 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 50 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 20
  50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 50 107 (accept_3_2 19 50
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 107
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 107 (accept_3_2 16 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 50 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 107 (Polychromatic418967fa.accept_11_3_6_8_1_1924
  14 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 107 (accept_3_2 13
  50 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 107
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 50 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 107 (accept_3_2 10 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 50 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 107 (Polychromatic418967fa.accept_12_8_2_11_1_246 8
  50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 107 (accept_3_2 7 50 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 50 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 50 107 (accept_3_2 4 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50
  107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 50 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 107 (accept_3_2 1 50 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 107)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 107 (allA_of_3_0 49 49
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 107 (allA_succ_of_accept 47 48 107
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 107 (accept_3_2 46 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 107 (Polychromatic418967fa.accept_13_5_9_3_1_870 44 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 107 (accept_3_2 43 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 48 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 107 (accept_3_2 40 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 107 (accept_3_2 37 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 48 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 107
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 107 (accept_3_2 34 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 107 (accept_3_2 31 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 107 (Polychromatic418967fa.accept_19_11_10_12_1_2256 30 48 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 107
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 107 (accept_3_2 28 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 107 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 107 (Polychromatic418967fa.accept_17_9_14_5_1_1555 26 48 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 107 (accept_3_2 25 48 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 48 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 107 (accept_3_2 22 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 107 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 107 (accept_3_2 19 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 48 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 107
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 107 (accept_3_2 16 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 107 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 107 (accept_3_2 13 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 107 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 48 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 107
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 107 (accept_3_2 10 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 107 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 107 (accept_3_2 7 48 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 48 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 107 (accept_3_2 4 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  107 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 107 (accept_3_2 1 48 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 107)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 107 (allA_succ_of_accept 46
  47 107 (accept_3_2 46 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 107
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 107 (accept_3_2 43 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 41
  47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 107 (accept_3_2 40 47
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 107
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 107 (accept_3_2 37 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 107 (Polychromatic418967fa.accept_13_9_8_3_1_3045
  35 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 107 (accept_3_2 34
  47 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 107
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 107 (accept_3_2 31 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 107
  (Polychromatic418967fa.accept_19_10_9_12_1_4774 29 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 107 (accept_3_2 28 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 107 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 107 (Polychromatic418967fa.accept_16_10_15_11_1_3785 26 47 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 107 (accept_3_2 25 47 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 107 (accept_3_2 22 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 107 (accept_3_2 19 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 107
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 107 (accept_3_2 16 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 107 (accept_3_2 13 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 107
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 107 (accept_3_2 10 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 107 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 107 (Polychromatic418967fa.accept_17_8_13_5_1_1597 8 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 107 (accept_3_2 7 47 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 47 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 107 (accept_3_2 4 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  107 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 47 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 107 (Polychromatic418967fa.accept_18_2_11_17_1_4773 2 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 107 (accept_3_2 1 47 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 107))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 107 (allA_of_3_0 46 46 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 107 (allA_succ_of_accept 44 45 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 107 (accept_3_2 43 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 107 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 107 (accept_3_2 40 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 107 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 45 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 107 (accept_3_2 37 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 107 (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 107 (accept_3_2 34 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 107 (accept_3_2 31 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 107 (accept_3_2 28 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 107 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 107 (accept_3_2 25 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 107 (Polychromatic418967fa.accept_16_8_13_11_1_4772 24 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 107 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 107 (accept_3_2 22 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 107 (Polychromatic418967fa.accept_23_21_22_15_1_4771 21 45 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 107 (accept_3_2 19 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 107 (Polychromatic418967fa.accept_21_17_3_2_1_2111 17 45 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 107 (accept_3_2 16 45 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 45 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 107 (accept_3_2 13 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 107 (Polychromatic418967fa.accept_19_11_7_12_1_4770 11 45 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 107 (accept_3_2 10 45 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 107 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 45 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 107 (accept_3_2 7 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 107 (accept_3_2 4 45 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 107 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 45 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 107 (accept_3_2 1 45 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 107))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  107 (allA_succ_of_accept 43 44 107 (accept_3_2 43 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 107 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 107 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 107 (accept_3_2 40 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 107
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 107 (accept_3_2 37 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 107 (Polychromatic418967fa.accept_16_4_12_11_1_2650 36 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 107 (Polychromatic418967fa.accept_13_9_5_3_1_428 35 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 107 (accept_3_2 34 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 107
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 107 (accept_3_2 31 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 107 (Polychromatic418967fa.accept_17_13_10_5_1_2566 30 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 107 (Polychromatic418967fa.accept_17_12_10_5_1_4756 29 44 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 107 (accept_3_2 28 44 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 107
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 107 (accept_3_2 25 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 107 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 107 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 107 (accept_3_2 22 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 107
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 107 (accept_3_2 19 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 107 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 107 (Polychromatic418967fa.accept_16_1_12_11_1_2648 17 44 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 107 (accept_3_2 16 44 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 107
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 107 (accept_3_2 13 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 107 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 107 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 107 (accept_3_2 10 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 107
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 107 (accept_3_2 7 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  107 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 107 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 107 (accept_3_2 4 44 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 107 (Polychromatic418967fa.accept_10_2_4_7_1_352 2
  44 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 107 (accept_3_2 1 44 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 107)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  107 (allA_of_3_0 43 43 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 107 (allA_succ_of_accept 41 42 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 107 (accept_3_2 40 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 107 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 107 (accept_3_2 37 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 107 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 42 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 107
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 107 (accept_3_2 34 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 107 (accept_3_2 31 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 42 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 107 (accept_3_2 28 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 107 (Polychromatic418967fa.accept_19_8_4_12_1_4768 27 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 107 (Polychromatic418967fa.accept_19_7_4_12_1_4769 26 42 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 107 (accept_3_2 25 42 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 107 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 42 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 107
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 107 (accept_3_2 22 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 107 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 107 (accept_3_2 19 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 107 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 42 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 107 (accept_3_2 16 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 107 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 107 (accept_3_2 13 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 42 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 107
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 107 (accept_3_2 10 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 107 (Polychromatic418967fa.accept_19_8_4_12_1_4768 8 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 107 (accept_3_2 7 42 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 42 107 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 42 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 107 (accept_3_2 4 42 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 107
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 107 (accept_3_2 1 42 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  107)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 107 (allA_succ_of_accept 40 41 107 (accept_3_2 40 41 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 39
  41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 107 (accept_3_2 37 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 107 (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 41 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 107 (accept_3_2 34 41 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 107 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 41 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 107
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 107 (accept_3_2 31 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 107 (accept_3_2 28 41 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 107 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 41 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 107 (accept_3_2 25 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 107 (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 41 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 107 (accept_3_2 22 41 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 41 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 107
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 107 (accept_3_2 19 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 107 (accept_3_2 16 41 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 41 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 107 (accept_3_2 13 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 41 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 107 (accept_3_2 10 41 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 107 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 41 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 107
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 107 (accept_3_2 7 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 107 (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 107 (accept_3_2 4 41 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 41 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 107 (accept_3_2 1 41 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 107))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 107
  (allA_of_3_0 40 40 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 107 (allA_succ_of_accept 38 39 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 107 (accept_3_2 37 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 107 (Polychromatic418967fa.accept_16_3_7_11_1_1723 35 39 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 107 (accept_3_2 34 39 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 39 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 107 (accept_3_2 31 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 107 (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 39 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 107 (accept_3_2 28 39 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 107 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 107 (accept_3_2 25 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 107 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 39 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 107 (accept_3_2 22 39 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 39 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 107 (accept_3_2 19 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 107 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 107 (Polychromatic418967fa.accept_20_17_19_7_1_4767 17 39 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 107 (accept_3_2 16 39 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 107 (accept_3_2 13 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 39 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 107 (accept_3_2 10 39 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 39 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 107 (accept_3_2 7 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  107 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 107 (accept_3_2 4 39 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 107 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 39 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 107 (accept_3_2 1 39 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 107))))))))))))))))))))))))))))))))))))))) (allB_succ 38 107
  (allA_succ_of_accept 37 38 107 (accept_3_2 37 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 107 (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 38 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 107 (accept_3_2 34 38 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 107 (accept_3_2 31 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 107 (accept_3_2 28 38 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 107
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 107 (accept_3_2 25 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 38 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 107 (accept_3_2 22 38 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 107
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 107 (accept_3_2 19 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 107 (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 107 (accept_3_2 16 38 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 107 (accept_3_2 13 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 107 (Polychromatic418967fa.accept_18_11_2_17_1_3490 11 38 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 107 (accept_3_2 10 38 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 107
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 107 (accept_3_2 7 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  107 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 107 (accept_3_2 4 38 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 107 (Polychromatic418967fa.accept_11_2_5_8_1_470 2
  38 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 107 (accept_3_2 1 38 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 107)))))))))))))))))))))))))))))))))))))) (allB_succ 37 107
  (allA_of_3_0 37 37 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 107 (allA_succ_of_accept 35 36 107
  (Polychromatic418967fa.accept_27_8_9_26_1_4766 35 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 107 (accept_3_2 34 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 107 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 107 (Polychromatic418967fa.accept_13_6_10_3_1_897 32 36 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 107 (accept_3_2 31 36 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 107 (Polychromatic418967fa.accept_21_9_15_2_1_4765 30 36 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 107
  (Polychromatic418967fa.accept_14_1_8_9_1_1312 29 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 107 (accept_3_2 28 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 107 (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 36 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 107 (accept_3_2 25 36 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 107 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 36 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 107
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 107 (accept_3_2 22 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 107 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 36 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 107 (accept_3_2 19 36 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 107 (Polychromatic418967fa.accept_19_18_17_12_1_4764 18 36 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 107
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 107 (accept_3_2 16 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 107 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 107 (Polychromatic418967fa.accept_17_14_2_5_1_3560 14 36 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 107 (accept_3_2 13 36 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 107 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 36
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 107
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 107 (accept_3_2 10 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 107 (Polychromatic418967fa.accept_16_9_4_11_1_2661 9 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 107 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 36 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 107 (accept_3_2 7 36 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 36 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 107
  (Polychromatic418967fa.accept_11_5_3_8_1_454 5 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 107 (accept_3_2 4 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  107 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 107 (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 107 (accept_3_2 1 36 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 107)))))))))))))))))))))))))))))))))))) (allB_succ 35 107 (allA_succ_of_accept 34 35 107
  (accept_3_2 34 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 107
  (Polychromatic418967fa.accept_10_3_5_7_1_330 33 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 107 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 107 (accept_3_2 31 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 107 (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 35 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 107 (Polychromatic418967fa.accept_15_14_5_2_1_4761
  29 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 107 (accept_3_2 28
  35 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 107
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 107 (Polychromatic418967fa.accept_14_12_7_9_1_726 26 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 107 (accept_3_2 25 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 107 (Polychromatic418967fa.accept_16_8_3_11_1_4763 24 35 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 107
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 107 (accept_3_2 22 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 107 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 107 (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 35 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 107 (accept_3_2 19 35 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 107 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 35 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 107
  (Polychromatic418967fa.accept_21_17_14_2_1_4762 17 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 107 (accept_3_2 16 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 107 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 107 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 35 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 107 (accept_3_2 13 35 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 107 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 35 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 107
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 107 (accept_3_2 10 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 107 (Polychromatic418967fa.accept_19_9_16_12_1_4760 9 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 107 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 35 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 107 (accept_3_2 7 35 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 107 (Polychromatic418967fa.accept_13_6_9_3_1_915 6 35 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 107
  (Polychromatic418967fa.accept_11_5_2_8_1_866 5 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 107 (accept_3_2 4 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  107 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 35 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 107 (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 107 (accept_3_2 1 35 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 107))))))))))))))))))))))))))))))))))) (allB_succ 34 107 (allA_of_3_0 34 34 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 33 107 (allA_succ_of_accept 32 33 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 107 (accept_3_2 31 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 107 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 33 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 107 (accept_3_2 28 33 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 107 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 33 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 107 (accept_3_2 25 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 33 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 107 (accept_3_2 22 33 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 107 (accept_3_2 19 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 33 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 107 (accept_3_2 16 33 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 107 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 33 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 107 (accept_3_2 13 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 33 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 107 (accept_3_2 10 33 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 107 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 33 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 107 (accept_3_2 7 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 33 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 107 (accept_3_2 4 33 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 107 (accept_3_2 1 33 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 107))))))))))))))))))))))))))))))))) (allB_succ 32 107
  (allA_succ_of_accept 31 32 107 (accept_3_2 31 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  32 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 107 (accept_3_2 28 32 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 107
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 107 (accept_3_2 25 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 107 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 107 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 32 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 107 (accept_3_2 22 32 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 107
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 107 (accept_3_2 19 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 107 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 107 (Polychromatic418967fa.accept_20_17_12_7_1_4759 17 32 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 107 (accept_3_2 16 32 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 107
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 107 (accept_3_2 13 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 107 (accept_3_2 10 32 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 107
  (Polychromatic418967fa.accept_22_8_10_19_1_4758 8 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 107 (accept_3_2 7 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  107 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 32 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 107 (accept_3_2 4 32 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 32
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 107 (accept_3_2 1 32 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 107)))))))))))))))))))))))))))))))) (allB_succ 31 107
  (allA_of_3_0 31 31 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 107 (allA_succ_of_accept 29 30 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 107 (accept_3_2 28 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 107 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 107 (Polychromatic418967fa.accept_17_9_13_5_1_3512 26 30 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 107 (accept_3_2 25 30 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 30 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 107 (accept_3_2 22 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 30 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 107 (accept_3_2 19 30 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 107 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 30 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 107 (accept_3_2 16 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 107 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 30 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 107 (accept_3_2 13 30 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 107 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 30 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 107
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 107 (accept_3_2 10 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 107 (Polychromatic418967fa.accept_17_8_13_5_1_1597 8 30 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 107 (accept_3_2 7 30 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 30 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 30 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 107 (accept_3_2 4 30 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 107 (Polychromatic418967fa.accept_16_3_14_11_1_2654
  3 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 107
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 107 (accept_3_2 1 30 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  107)))))))))))))))))))))))))))))) (allB_succ 29 107 (allA_succ_of_accept 28 29 107 (accept_3_2 28 29 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 29 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 107 (accept_3_2 25 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 107 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 29 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 107 (accept_3_2 22 29 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 29 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 107
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 107 (accept_3_2 19 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 107 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 107 (accept_3_2 16 29 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 29 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 107 (accept_3_2 13 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 107 (Polychromatic418967fa.accept_19_11_10_12_1_2256 11 29 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 107 (accept_3_2 10 29 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 107 (Polychromatic418967fa.accept_17_9_12_5_1_219 9 29 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 107
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 107 (accept_3_2 7 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 107 (accept_3_2 4 29 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 107 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 29 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 107 (accept_3_2 1 29 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 107))))))))))))))))))))))))))))) (allB_succ 28 107 (allA_of_3_0
  28 28 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 107 (allA_succ_of_accept 26 27 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 107 (accept_3_2 25 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 107 (Polychromatic418967fa.accept_19_4_8_12_1_4757 23 27 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 107 (accept_3_2 22 27 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 107 (accept_3_2 19 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 27 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 107 (accept_3_2 16 27 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 107 (accept_3_2 13 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 107 (Polychromatic418967fa.accept_17_12_10_5_1_4756 12 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 27 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 107 (accept_3_2 10 27 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 27 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 107 (accept_3_2 7 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  107 (Polychromatic418967fa.accept_13_6_1_3_1_1522 6 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 27 107 (Polychromatic418967fa.accept_13_5_1_3_1_878 5 27 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 107 (accept_3_2 4 27 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 107 (accept_3_2 1 27 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  107))))))))))))))))))))))))))) (allB_succ 26 107 (allA_succ_of_accept 25 26 107 (accept_3_2 25 26 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 26 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 107
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 107 (accept_3_2 22 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 107 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 26 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 107 (accept_3_2 19 26 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 26 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 107 (accept_3_2 16 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 107 (Polychromatic418967fa.accept_17_14_9_5_1_4755 14 26 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 107 (accept_3_2 13 26 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 107 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 26 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 107
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 107 (accept_3_2 10 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 107 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 26 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 107 (accept_3_2 7 26 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 107 (Polychromatic418967fa.accept_15_6_11_2_1_2801 6 26 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 107 (accept_3_2 4 26 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 107
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 2 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 107 (accept_3_2 1 26 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  107)))))))))))))))))))))))))) (allB_succ 25 107 (allA_of_3_0 25 25 107 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 107 (allA_succ_of_accept 23 24 107 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 24 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 107 (accept_3_2 22 24 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 107
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 107 (accept_3_2 19 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 107 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 107 (Polychromatic418967fa.accept_19_17_5_12_1_4753 17 24 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 107 (accept_3_2 16 24 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 107
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 107 (accept_3_2 13 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 107 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 107 (accept_3_2 10 24 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 107 (Polychromatic418967fa.accept_17_9_7_5_1_1566 9 24 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 107
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 107 (accept_3_2 7 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  107 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 107 (accept_3_2 4 24 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 24 107 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 107 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  24 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 107 (accept_3_2 1 24 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 107)))))))))))))))))))))))) (allB_succ 23 107
  (allA_succ_of_accept 22 23 107 (accept_3_2 22 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  23 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 23 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 107 (accept_3_2 19 23 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 107 (Polychromatic418967fa.accept_16_2_7_11_1_1698 18 23 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 107
  (Polychromatic418967fa.accept_24_17_23_11_1_4752 17 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 23 107 (accept_3_2 16 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 23 107 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 23 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 107 (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 23 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 107 (accept_3_2 13 23 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 12
  23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 107
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 107 (accept_3_2 10 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 107 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 107 (Polychromatic418967fa.accept_18_8_5_17_1_1388 8 23 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 107 (accept_3_2 7 23 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 107 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 23 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 107
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 107 (accept_3_2 4 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  107 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 23 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 107 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 107 (accept_3_2 1 23 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 107))))))))))))))))))))))) (allB_succ 22 107 (allA_of_3_0 22 22 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 107 (allA_succ_of_accept 20 21 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 107 (accept_3_2 19 21 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 107
  (Polychromatic418967fa.accept_19_17_2_12_1_4751 17 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 107 (accept_3_2 16 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 107 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 107 (accept_3_2 13 21 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 107 (Polychromatic418967fa.accept_14_12_7_9_1_726 12 21 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 107
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 107 (accept_3_2 10 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 107 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 107 (accept_3_2 7 21 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 107 (accept_3_2 4 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  107 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 107 (accept_3_2 1 21 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 107))))))))))))))))))))) (allB_succ 20 107 (allA_succ_of_accept 19 20 107
  (accept_3_2 19 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 107
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 107 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 107 (accept_3_2 16 20 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 107 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 107 (accept_3_2 13 20
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 107
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 107 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 107 (accept_3_2 10 20 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 107 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 20
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 107 (accept_3_2 7 20 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 107 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 107
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 107 (accept_3_2 4 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 107 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 20 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 107 (accept_3_2 1 20 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 107)))))))))))))))))))) (allB_succ 19 107 (allA_of_3_0 19 19 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 107 (allA_succ_of_accept 17 18 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 107 (accept_3_2 16 18 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 107 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  15 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 107
  (Polychromatic418967fa.accept_13_1_5_3_1_888 14 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 107 (accept_3_2 13 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 107 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 18 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 107 (accept_3_2 10 18 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 107
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 107 (accept_3_2 7 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  107 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 107 (accept_3_2 4 18 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 107 (Polychromatic418967fa.accept_21_3_18_2_1_4750 3 18 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 107 (Polychromatic418967fa.accept_13_2_5_3_1_406 2
  18 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 107 (accept_3_2 1 18 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 107)))))))))))))))))) (allB_succ 17 107 (allA_succ_of_accept 16
  17 107 (accept_3_2 16 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 107
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 107 (accept_3_2 13 17 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 107 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 107
  (Polychromatic418967fa.accept_21_11_17_2_1_4749 11 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 107 (accept_3_2 10 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 107 (Polychromatic418967fa.accept_20_9_17_7_1_4748 9 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 107 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 107 (accept_3_2 7 17 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 107
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 107 (accept_3_2 4 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  107 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 17 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 17 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 107 (accept_3_2 1 17 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 17 107))))))))))))))))) (allB_succ 16 107 (allA_of_3_0 16 16 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 15 107 (allA_succ_of_accept 14 15 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 107 (accept_3_2 13 15 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 107 (Polychromatic418967fa.accept_8_4_7_3_1_144 12
  15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 107
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 107 (accept_3_2 10 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  15 107 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 15 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 107 (accept_3_2 7 15 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 107 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 107
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 107 (accept_3_2 4 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15
  107 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 107 (accept_3_2 1 15 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 15 107))))))))))))))) (allB_succ 14 107 (allA_succ_of_accept 13 14 107 (accept_3_2 13 14 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 107 (Polychromatic418967fa.accept_9_3_5_8_1_99 12
  14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 107
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 107 (accept_3_2 10 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 107 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 14 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 107 (accept_3_2 7 14 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 14 107 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 14 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 107 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 107 (accept_3_2 4 14 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 107
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 107 (accept_3_2 1 14 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  107)))))))))))))) (allB_succ 13 107 (allA_of_3_0 13 13 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 107
  (allA_succ_of_accept 11 12 107 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 107 (accept_3_2 10 12 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 107 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 12 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 107 (Polychromatic418967fa.accept_16_8_12_11_1_3697
  8 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 107 (accept_3_2 7 12
  107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 107 (Polychromatic418967fa.accept_9_6_3_8_1_595
  6 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 107
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 107 (accept_3_2 4 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  107 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 107 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 12 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 107 (accept_3_2 1 12 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 107)))))))))))) (allB_succ 11 107 (allA_succ_of_accept 10 11 107 (accept_3_2 10 11 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 107 (Polychromatic418967fa.accept_15_9_11_2_1_1882
  9 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 107
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 107 (accept_3_2 7 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  107 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 107 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 11 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 107 (accept_3_2 4 11 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 107 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 11 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 107 (Polychromatic418967fa.accept_13_2_11_3_1_873 2
  11 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 107 (accept_3_2 1 11 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 107))))))))))) (allB_succ 10 107 (allA_of_3_0 10 10 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 107 (allA_succ_of_accept 8 9 107
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 107 (accept_3_2 7 9 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 107 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 9 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 107 (accept_3_2 4 9 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 107 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 9 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 107 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 107 (accept_3_2 1 9 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 107))))))))) (allB_succ 8 107 (allA_succ_of_accept 7 8 107
  (accept_3_2 7 8 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 107
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 8 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 107 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 8 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 107 (accept_3_2 4 8 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 107 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 107 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 8
  107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 107 (accept_3_2 1 8 107
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 107)))))))) (allB_succ 7 107 (allA_of_3_0 7 7 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 6 107 (allA_succ_of_accept 5 6 107
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 107 (accept_3_2 4 6 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 107
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 107 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 6 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 107 (accept_3_2 1 6 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 107)))))) (allB_succ 5 107 (allA_succ_of_accept 4 5 107 (accept_3_2 4 5 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 107 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 5 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 107
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 107 (accept_3_2 1 5 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 107)))))
  (allB_succ 4 107 (allA_of_3_0 4 4 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 107 (allA_succ_of_accept 2
  3 107 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 107 (accept_3_2 1 3 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 107)))
  (allB_succ 2 107 (allA_succ_of_accept 1 2 107 (accept_3_2 1 2 107 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  107)) (allB_two
  107)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


