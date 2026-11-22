-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch89
-- name    : Polychromatic418967fa_Branch89
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:00.783173+00:00
-- url     : https://prove2.me/theorems/0eee980d-16f8-4527-918c-d4e2f0483ed6
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

def Polychromatic418967fa.branch_89 : allB 89 89 :=
  allB_succ' 2 88 89 (Eq.refl Bool.true) (allA_of_3_0 2 88 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3 87
  89 (Eq.refl Bool.true) (allA_succ_of_accept 2 87 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 89 (accept_3_2 1 87 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87 89))) (allB_succ' 4 86 89 (Eq.refl Bool.true) (allA_succ_of_accept 3 86
  89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 86 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 86 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 89 (accept_3_2 1 86 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 89)))) (allB_succ' 5 85 89 (Eq.refl Bool.true) (allA_of_3_0 5 85 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 84 89 (Eq.refl Bool.true) (allA_succ_of_accept 5 84 89
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 89 (accept_3_2 4 84 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 89
  (Polychromatic418967fa.accept_10_3_4_9_1_15 3 84 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 84 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 89 (accept_3_2 1 84 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 89)))))) (allB_succ' 7 83 89 (Eq.refl Bool.true) (allA_succ_of_accept 6 83 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 89 (accept_3_2 4 83 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 89 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 83 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 89 (accept_3_2 1 83 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83 89))))))) (allB_succ' 8 82 89 (Eq.refl Bool.true) (allA_of_3_0 8
  82 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 81 89 (Eq.refl Bool.true) (allA_succ_of_accept 8 81 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 89 (accept_3_2 7 81 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 89
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 89 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 81 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 89 (accept_3_2 4 81 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 89 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 89 (accept_3_2 1 81 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 89))))))))) (allB_succ' 10 80 89 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 89 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 80 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 89 (accept_3_2 7 80 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 89 (Polychromatic418967fa.accept_15_6_5_14_1_429 6 80 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 80 89
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 5 80 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 80 89 (accept_3_2 4 80 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 89
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 80 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 80 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 89 (accept_3_2 1 80 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 89)))))))))) (allB_succ' 11 79 89 (Eq.refl Bool.true) (allA_of_3_0 11 79 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 78 89 (Eq.refl Bool.true) (allA_succ_of_accept 11 78 89
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 89 (accept_3_2 10 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 78
  89 (Polychromatic418967fa.accept_21_9_15_5_1_3500 9 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 89 (Polychromatic418967fa.accept_19_8_2_13_1_2328 8 78 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 89 (accept_3_2 7 78 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 89 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 78 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 89 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 78
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 89 (accept_3_2 4 78 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 89
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 89 (accept_3_2 1 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 89))))))))))))
  (allB_succ' 13 77 89 (Eq.refl Bool.true) (allA_succ_of_accept 12 77 89 (Polychromatic418967fa.accept_8_4_5_1_1_299 12
  77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 89
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 89 (accept_3_2 10 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77
  89 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 77 89 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 77 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 89 (accept_3_2 7 77 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 77 89 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 89 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5
  77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 89 (accept_3_2 4 77 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 89 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 77
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 89
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 89 (accept_3_2 1 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 89)))))))))))))
  (allB_succ' 14 76 89 (Eq.refl Bool.true) (allA_of_3_0 14 76 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15
  75 89 (Eq.refl Bool.true) (allA_succ_of_accept 14 75 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 89 (accept_3_2 13 75 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 89 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 75
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 89
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 89 (accept_3_2 10 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75
  89 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 89 (accept_3_2 7 75 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 75
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 89 (accept_3_2 4 75 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 89 (Polychromatic418967fa.accept_13_3_10_11_1_1293
  3 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 89 (accept_3_2 1 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  89))))))))))))))) (allB_succ' 16 74 89 (Eq.refl Bool.true) (allA_succ_of_accept 15 74 89
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 74 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 74 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 89 (accept_3_2 13 74 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 74 89 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 74 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 89 (accept_3_2 10 74 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 89
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 89 (accept_3_2 7 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 89
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 74 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 89 (accept_3_2 4 74 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 74
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 89 (accept_3_2 1 74 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 89)))))))))))))))) (allB_succ' 17 73 89 (Eq.refl Bool.true)
  (allA_of_3_0 17 73 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 72 89 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 89 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 89 (accept_3_2 16 72 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 89 (Polychromatic418967fa.accept_16_15_8_9_1_2563 15 72 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 89 (Polychromatic418967fa.accept_13_1_7_11_1_702
  14 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 89 (accept_3_2 13 72
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 89
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 89 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 89 (accept_3_2 10 72 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 89 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 72 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 89 (Polychromatic418967fa.accept_23_8_3_20_1_3499 8
  72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 89 (accept_3_2 7 72 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 89 (Polychromatic418967fa.accept_19_6_15_13_1_3498
  6 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 89
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 89 (accept_3_2 4 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 89
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 89 (Polychromatic418967fa.accept_15_2_12_14_1_1709 2 72 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 89 (accept_3_2 1 72 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 89)))))))))))))))))) (allB_succ' 19 71 89 (Eq.refl Bool.true) (allA_succ_of_accept 18 71 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 71 89 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 71 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 89 (accept_3_2 16 71 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 71 89 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 71 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 89 (accept_3_2 13 71 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 89 (Polychromatic418967fa.accept_10_2_1_9_1_1248
  12 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 89
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 89 (accept_3_2 10 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71
  89 (Polychromatic418967fa.accept_22_9_5_1_1_2204 9 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 71 89 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 71 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 89 (accept_3_2 7 71 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 71 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 89 (Polychromatic418967fa.accept_10_5_1_9_1_791 5
  71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 89 (accept_3_2 4 71 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 89 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 71
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 89 (accept_3_2 1 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  89))))))))))))))))))) (allB_succ' 20 70 89 (Eq.refl Bool.true) (allA_of_3_0 20 70 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 69 89 (Eq.refl Bool.true) (allA_succ_of_accept 20 69 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 89 (accept_3_2 19 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69
  89 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 89 (Polychromatic418967fa.accept_16_1_5_9_1_1649 17 69 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 89 (accept_3_2 16 69 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 89 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 14
  69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 89 (accept_3_2 13 69 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 89 (Polychromatic418967fa.accept_8_4_5_1_1_299 12
  69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 89
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 89 (accept_3_2 10 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69
  89 (Polychromatic418967fa.accept_18_9_15_17_1_3497 9 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 89 (accept_3_2 7 69 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 69 89 (Polychromatic418967fa.accept_13_6_4_11_1_282 6 69 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 89 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 69
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 89 (accept_3_2 4 69 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 89 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 89 (accept_3_2 1 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  89))))))))))))))))))))) (allB_succ' 22 68 89 (Eq.refl Bool.true) (allA_succ_of_accept 21 68 89
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 68 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 68 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 89 (accept_3_2 19 68 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 68 89 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 68 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 89 (Polychromatic418967fa.accept_10_7_8_9_1_785 17
  68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 89 (accept_3_2 16 68 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 89
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 89 (accept_3_2 13 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68
  89 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 68 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 68 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 89 (accept_3_2 10 68 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 68 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 89 (Polychromatic418967fa.accept_13_8_3_11_1_3467 8
  68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 89 (accept_3_2 7 68 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 89 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 68
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 89
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 89 (accept_3_2 4 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68 89
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 68 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 89 (accept_3_2 1 68 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 89)))))))))))))))))))))) (allB_succ' 23 67 89 (Eq.refl Bool.true) (allA_of_3_0 23 67 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 66 89 (Eq.refl Bool.true) (allA_succ_of_accept 23 66 89
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 89 (accept_3_2 22 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66
  89 (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 66 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 89 (accept_3_2 19 66 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 89 (Polychromatic418967fa.accept_19_18_9_13_1_3496 18 66 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 89
  (Polychromatic418967fa.accept_16_1_2_9_1_1607 17 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 89 (accept_3_2 16 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66
  89 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 66 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 89 (accept_3_2 13 66 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 89 (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 66 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 89 (accept_3_2 10 66 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 89
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 66 89 (accept_3_2 7 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 89
  (Polychromatic418967fa.accept_9_6_3_8_1_595 6 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 66 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 89 (accept_3_2 4 66 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 66 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 66
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 89 (accept_3_2 1 66 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 89)))))))))))))))))))))))) (allB_succ' 25 65 89 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 65 89 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 89 (accept_3_2 22 65 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 89 (Polychromatic418967fa.accept_9_3_2_8_1_108 21
  65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 89
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 89 (accept_3_2 19 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65
  89 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 89 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 89 (accept_3_2 16 65 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 65 89 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 65 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 89 (accept_3_2 13 65 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 89 (Polychromatic418967fa.accept_9_3_2_8_1_108 12
  65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 89
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 89 (accept_3_2 10 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65
  89 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 89 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 65 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 89 (accept_3_2 7 65 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 89 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 65 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 89 (accept_3_2 4 65 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 89 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 65
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 89
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 89 (accept_3_2 1 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  89))))))))))))))))))))))))) (allB_succ' 26 64 89 (Eq.refl Bool.true) (allA_of_3_0 26 64 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 63 89 (Eq.refl Bool.true) (allA_succ_of_accept 26 63 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 89 (accept_3_2 25 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63
  89 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 89 (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 89 (accept_3_2 22 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 63 89 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 20
  63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 89 (accept_3_2 19 63 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 89
  (Polychromatic418967fa.accept_15_2_3_14_1_972 17 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 89 (accept_3_2 16 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63
  89 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 89 (accept_3_2 13 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 89 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 63 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 89 (Polychromatic418967fa.accept_15_11_3_14_1_971
  11 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 89 (accept_3_2 10 63
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 89 (Polychromatic418967fa.accept_12_9_3_5_1_423
  9 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 89 (accept_3_2 7 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 89 (Polychromatic418967fa.accept_23_5_17_20_1_3495 5 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 89 (accept_3_2 4 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 89 (Polychromatic418967fa.accept_23_3_17_20_1_3494 3 63 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 89 (accept_3_2 1 63 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 89))))))))))))))))))))))))))) (allB_succ' 28 62 89 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 62 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 89 (Polychromatic418967fa.accept_19_7_5_13_1_3493
  26 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 89 (accept_3_2 25 62
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 89
  (Polychromatic418967fa.accept_20_4_2_9_1_1261 24 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 62 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 89 (accept_3_2 22 62 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 62 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 89 (Polychromatic418967fa.accept_12_8_2_5_1_844 20
  62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 89 (accept_3_2 19 62 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 89 (Polychromatic418967fa.accept_7_4_6_5_1_141 18
  62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 89
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 89 (accept_3_2 16 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 62
  89 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 62 89 (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 62 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 89 (accept_3_2 13 62 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 62 89 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 62 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 89
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 89 (accept_3_2 10 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 62
  89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 62 89 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 62 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 89 (accept_3_2 7 62 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 62 89 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 62 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 89 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5
  62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 89 (accept_3_2 4 62 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 89
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 2 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 62 89 (accept_3_2 1 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  89)))))))))))))))))))))))))))) (allB_succ' 29 61 89 (Eq.refl Bool.true) (allA_of_3_0 29 61 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 60 89 (Eq.refl Bool.true) (allA_succ_of_accept 29 60 89
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 89 (accept_3_2 28 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60
  89 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 60 89 (Polychromatic418967fa.accept_19_7_3_13_1_3492 26 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 89 (accept_3_2 25 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 60 89 (Polychromatic418967fa.accept_16_8_12_9_1_2569 24 60 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 23
  60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 89 (accept_3_2 22 60 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 89 (Polychromatic418967fa.accept_8_5_4_1_1_111 21
  60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 89
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 60 89 (accept_3_2 19 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60
  89 (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 60 89 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 60 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 89 (accept_3_2 16 60 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 60 89 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 89
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 60 89 (accept_3_2 13 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60
  89 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 89 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 89 (accept_3_2 10 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 89 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 60
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 89 (accept_3_2 7 60 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 89 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 60
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 89
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 89 (accept_3_2 4 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 89
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 89 (accept_3_2 1 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 89)))))))))))))))))))))))))))))) (allB_succ' 31 59 89 (Eq.refl Bool.true)
  (allA_succ_of_accept 30 59 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 89 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 59 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 89 (accept_3_2 28 59 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 89 (Polychromatic418967fa.accept_13_1_7_11_1_702
  27 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 89 (accept_3_2 25 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59
  89 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 59 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 89 (accept_3_2 22 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 59 89 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 59 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 89 (accept_3_2 19 59 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 89
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 17 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 89 (accept_3_2 16 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59
  89 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 59 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 89 (accept_3_2 13 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 59 89 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 11
  59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 89 (accept_3_2 10 59 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 59
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 89
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 89 (accept_3_2 7 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 89 (Polychromatic418967fa.accept_13_5_7_11_1_3470 5 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 89 (accept_3_2 4 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 89 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 59 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 89 (accept_3_2 1 59 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 89))))))))))))))))))))))))))))))) (allB_succ' 32 58 89 (Eq.refl
  Bool.true) (allA_of_3_0 32 58 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 57 89 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 89 (accept_3_2 31 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 89 (Polychromatic418967fa.accept_20_10_17_9_1_3491 30 57 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 29
  57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 89 (accept_3_2 28 57 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 89 (Polychromatic418967fa.accept_7_6_1_5_1_322 27
  57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 89 (accept_3_2 25 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57
  89 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 89 (accept_3_2 22 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 89 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 57 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 20
  57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 89 (accept_3_2 19 57 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 89 (Polychromatic418967fa.accept_7_4_1_5_1_540 18
  57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 89
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 89 (accept_3_2 16 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57
  89 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 89 (accept_3_2 13 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 89 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 57 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 89 (Polychromatic418967fa.accept_7_4_1_5_1_540 11
  57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 89 (accept_3_2 10 57 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 89 (Polychromatic418967fa.accept_15_9_12_14_1_963 9
  57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 89 (accept_3_2 7 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 89
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 89 (accept_3_2 4 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 89 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 89 (accept_3_2 1 57 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 89))))))))))))))))))))))))))))))))) (allB_succ' 34 56 89
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 89
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 89 (accept_3_2 31 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 56
  89 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 56 89 (Polychromatic418967fa.accept_18_11_2_17_1_3490 29 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 89 (accept_3_2 28 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 56 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 89 (Polychromatic418967fa.accept_12_2_8_5_1_408 26
  56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 89 (accept_3_2 25 56 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56 89 (Polychromatic418967fa.accept_9_6_2_8_1_592 24
  56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 89
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 56 89 (accept_3_2 22 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 56
  89 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 56 89 (Polychromatic418967fa.accept_13_7_4_11_1_1967 20 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 89 (accept_3_2 19 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 56 89 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 56 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 89 (Polychromatic418967fa.accept_16_1_8_9_1_3462
  17 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 89 (accept_3_2 16 56
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 89 (Polychromatic418967fa.accept_6_3_2_5_1_32
  15 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 89
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 89 (accept_3_2 13 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56
  89 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 56 89 (Polychromatic418967fa.accept_18_11_2_17_1_3490 11 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 89 (accept_3_2 10 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 56 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 89 (Polychromatic418967fa.accept_13_8_4_11_1_3469 8
  56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 56 89 (accept_3_2 7 56 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56 89 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 56
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 89
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 56 89 (accept_3_2 4 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 89
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 56 89 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 89 (accept_3_2 1 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 89)))))))))))))))))))))))))))))))))) (allB_succ' 35 55 89 (Eq.refl Bool.true) (allA_of_3_0 35
  55 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 54 89 (Eq.refl Bool.true) (allA_succ_of_accept 35 54 89
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 89 (accept_3_2 34 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 54
  89 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 54 89 (Polychromatic418967fa.accept_21_11_12_5_1_2224 32 54 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 89 (accept_3_2 31 54 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 54 89 (Polychromatic418967fa.accept_13_4_2_11_1_733 30 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 89 (Polychromatic418967fa.accept_13_3_2_11_1_1999
  29 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 89 (accept_3_2 28 54
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 89 (Polychromatic418967fa.accept_4_3_2_1_1_50
  27 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 89
  (Polychromatic418967fa.accept_20_6_14_9_1_3489 26 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 89 (accept_3_2 25 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54
  89 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 89 (accept_3_2 22 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 89 (Polychromatic418967fa.accept_14_7_12_5_1_1861 21 54 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 89
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 89 (accept_3_2 19 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54
  89 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 89 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 54 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 89 (accept_3_2 16 54 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 89
  (Polychromatic418967fa.accept_19_14_16_13_1_3488 14 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 89 (accept_3_2 13 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54
  89 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 89 (accept_3_2 10 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 89 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 54 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 89
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 89 (accept_3_2 7 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 89
  (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 89 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 54 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 89 (accept_3_2 4 54 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 89 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2
  54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 89 (accept_3_2 1 54 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 89)))))))))))))))))))))))))))))))))))) (allB_succ' 37 53 89
  (Eq.refl Bool.true) (allA_succ_of_accept 36 53 89 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 89
  (Polychromatic418967fa.accept_13_9_1_11_1_275 35 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 89 (accept_3_2 34 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53
  89 (Polychromatic418967fa.accept_13_7_1_11_1_732 33 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 53 89 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 89 (accept_3_2 31 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 53 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 89 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 89 (accept_3_2 28 53 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 89 (Polychromatic418967fa.accept_7_6_4_5_1_314 27
  53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 89
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 89 (accept_3_2 25 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53
  89 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 53 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 89 (accept_3_2 22 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 53 89 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 89 (Polychromatic418967fa.accept_7_6_4_5_1_314 20
  53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 89 (accept_3_2 19 53 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 89 (Polychromatic418967fa.accept_21_18_11_5_1_3487
  18 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 89
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 17 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 89 (accept_3_2 16 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53
  89 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 53 89 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 89 (accept_3_2 13 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 53 89 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 89 (Polychromatic418967fa.accept_16_11_5_9_1_1617
  11 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 89 (accept_3_2 10 53
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 9
  53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 89
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 89 (accept_3_2 7 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 89
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 89 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 89 (accept_3_2 4 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 89 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 53
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 89 (accept_3_2 1 53 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 89))))))))))))))))))))))))))))))))))))) (allB_succ' 38 52 89
  (Eq.refl Bool.true) (allA_of_3_0 38 52 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 51 89 (Eq.refl
  Bool.true) (allA_succ_of_accept 38 51 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 89 (accept_3_2 37 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 89 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 51 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 89
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 89 (accept_3_2 34 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51
  89 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 89 (accept_3_2 31 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 89 (Polychromatic418967fa.accept_9_2_6_8_1_321 29
  51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 89 (accept_3_2 28 51 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 89 (Polychromatic418967fa.accept_13_1_12_11_1_728
  27 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 89 (accept_3_2 25 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51
  89 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 89 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 89 (accept_3_2 22 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 89 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 20
  51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 89 (accept_3_2 19 51 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 89
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 89 (accept_3_2 16 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51
  89 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 89 (accept_3_2 13 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 89 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 89 (Polychromatic418967fa.accept_7_4_2_5_1_527 11
  51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 89 (accept_3_2 10 51 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 89 (Polychromatic418967fa.accept_12_9_3_5_1_423 9
  51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 89 (accept_3_2 7 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 89 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 89 (accept_3_2 4 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 89 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 89 (accept_3_2 1 51 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 89))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 50 89
  (Eq.refl Bool.true) (allA_succ_of_accept 39 50 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 89
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 89 (accept_3_2 37 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50
  89 (Polychromatic418967fa.accept_15_6_5_14_1_429 36 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 89 (accept_3_2 34 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 89 (Polychromatic418967fa.accept_7_4_1_5_1_540 32
  50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 89 (accept_3_2 31 50 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 89 (Polychromatic418967fa.accept_9_3_5_8_1_99 30
  50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 50 89
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 50 89 (accept_3_2 28 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50
  89 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 50 89 (Polychromatic418967fa.accept_20_6_10_9_1_3486 26 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 50 89 (accept_3_2 25 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 50 89 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 50 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 89 (accept_3_2 22 50 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 89
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 89 (accept_3_2 19 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50
  89 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 89 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 89 (accept_3_2 16 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 50 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 89
  (Polychromatic418967fa.accept_19_14_12_13_1_3485 14 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 89 (accept_3_2 13 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50
  89 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 50 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 89 (accept_3_2 10 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 50 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 89 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 89 (accept_3_2 7 50 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 89 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 50
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 50 89
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 50 89 (accept_3_2 4 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 89
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 50 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 89 (accept_3_2 1 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 89)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 49 89 (Eq.refl Bool.true)
  (allA_of_3_0 41 49 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 48 89 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 89 (accept_3_2 40 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 89 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 38
  48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 89 (accept_3_2 37 48 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 89 (Polychromatic418967fa.accept_7_1_6_5_1_39 36
  48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 89
  (Polychromatic418967fa.accept_17_1_14_4_1_1550 35 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 89 (accept_3_2 34 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 48
  89 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 48 89 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 89 (accept_3_2 31 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 48 89 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 48 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 89 (Polychromatic418967fa.accept_7_1_6_5_1_39 29
  48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 89 (accept_3_2 28 48 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 89 (Polychromatic418967fa.accept_10_7_8_9_1_785 27
  48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 89
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 89 (accept_3_2 25 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48
  89 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 89 (accept_3_2 22 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 89 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 48 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 20
  48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 89 (accept_3_2 19 48 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 89 (Polychromatic418967fa.accept_7_4_6_5_1_141 18
  48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 89
  (Polychromatic418967fa.accept_10_7_8_9_1_785 17 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 89 (accept_3_2 16 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48
  89 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 48 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 89 (accept_3_2 13 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 48 89 (Polychromatic418967fa.accept_21_12_6_5_1_3484 12 48 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 89 (Polychromatic418967fa.accept_7_4_6_5_1_141 11
  48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 89 (accept_3_2 10 48 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 89 (Polychromatic418967fa.accept_17_9_14_4_1_3483 9
  48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 89
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 89 (accept_3_2 7 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 89
  (Polychromatic418967fa.accept_9_6_3_8_1_595 6 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 89 (accept_3_2 4 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 48 89 (Polychromatic418967fa.accept_19_3_10_13_1_3482 3 48 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 48
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 89 (accept_3_2 1 48 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 89)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 47
  89 (Eq.refl Bool.true) (allA_succ_of_accept 42 47 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 89
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 89 (accept_3_2 40 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47
  89 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 89 (accept_3_2 37 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 89 (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 47 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 89 (Polychromatic418967fa.accept_11_2_3_1_1_244 35
  47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 89 (accept_3_2 34 47 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 89 (Polychromatic418967fa.accept_9_6_2_8_1_592 33
  47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 89
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 89 (accept_3_2 31 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47
  89 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 47 89 (Polychromatic418967fa.accept_13_3_8_11_1_1906 29 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 89 (accept_3_2 28 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 47 89 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 47 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 89 (accept_3_2 25 47 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 89 (Polychromatic418967fa.accept_9_6_2_8_1_592 24
  47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 89
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 89 (accept_3_2 22 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47
  89 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 89 (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 89 (accept_3_2 19 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 89 (Polychromatic418967fa.accept_13_4_8_11_1_1937
  17 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 89 (accept_3_2 16 47
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 89 (Polychromatic418967fa.accept_9_6_2_8_1_592
  15 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 89 (accept_3_2 13 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47
  89 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 47 89 (Polychromatic418967fa.accept_22_11_3_1_1_3481 11 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 89 (accept_3_2 10 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 47 89 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 47 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 89 (Polychromatic418967fa.accept_10_8_7_9_1_425 8
  47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 89 (accept_3_2 7 47 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 89
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 89 (accept_3_2 4 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 89
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 89 (accept_3_2 1 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 47 89))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 46 89 (Eq.refl Bool.true) (allA_of_3_0 44 46
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 89 (allA_succ_of_accept 44 45 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 89 (accept_3_2 43 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45
  89 (Polychromatic418967fa.accept_19_4_7_13_1_3480 42 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 89 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 89 (accept_3_2 40 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 89 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 45 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 89 (accept_3_2 37 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45
  89 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 89 (Polychromatic418967fa.accept_20_15_5_9_1_3479 35 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 89 (accept_3_2 34 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 89 (Polychromatic418967fa.accept_16_1_13_9_1_2551 33 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 32
  45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 89 (accept_3_2 31 45 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 30
  45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 89
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 89 (accept_3_2 28 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45
  89 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 89 (accept_3_2 25 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 89 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 23
  45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 89 (accept_3_2 22 45 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 89 (Polychromatic418967fa.accept_10_1_5_9_1_157 21
  45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 89 (accept_3_2 19 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45
  89 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 89 (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 89 (accept_3_2 16 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 89 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 45 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 89 (accept_3_2 13 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45
  89 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 89 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 89 (accept_3_2 10 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 89 (accept_3_2 7 45 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 89 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6
  45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 89
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 89 (accept_3_2 4 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 89
  (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 89 (accept_3_2 1 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 45 89))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 89 (allA_succ_of_accept 43 44
  89 (accept_3_2 43 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 89
  (Polychromatic418967fa.accept_13_3_5_11_1_716 42 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 89 (Polychromatic418967fa.accept_18_5_8_17_1_3478 41 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 89 (accept_3_2 40 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 89 (Polychromatic418967fa.accept_7_3_2_5_1_147 38
  44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 89 (accept_3_2 37 44 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 89 (Polychromatic418967fa.accept_16_4_12_9_1_2567
  36 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 44 89
  (Polychromatic418967fa.accept_10_5_4_9_1_420 35 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 44 89 (accept_3_2 34 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 44
  89 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 44 89 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 89 (accept_3_2 31 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 44 89 (Polychromatic418967fa.accept_19_11_6_13_1_3477 30 44 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 89 (Polychromatic418967fa.accept_8_5_4_1_1_111 29
  44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 89 (accept_3_2 28 44 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 89
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 89 (accept_3_2 25 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44
  89 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 89 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 89 (accept_3_2 22 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 89 (Polychromatic418967fa.accept_13_7_5_11_1_1927
  20 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 89 (accept_3_2 19 44
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 89 (Polychromatic418967fa.accept_7_4_2_5_1_527
  18 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 89
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 89 (accept_3_2 16 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 44
  89 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 44 89 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 89 (accept_3_2 13 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 44 89 (Polychromatic418967fa.accept_19_12_6_13_1_2305 12 44 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 89 (Polychromatic418967fa.accept_7_4_2_5_1_527 11
  44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 89 (accept_3_2 10 44 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 89
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 89 (accept_3_2 7 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 89
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 89 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 89 (accept_3_2 4 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 89 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 89 (accept_3_2 1 44 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 89)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 89
  (allA_of_3_0 43 43 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 89 (allA_succ_of_accept 41 42 89
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 89 (accept_3_2 40 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42
  89 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 42 89 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 89 (accept_3_2 37 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 42 89 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 89 (accept_3_2 34 42 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 89 (Polychromatic418967fa.accept_13_7_3_11_1_280
  33 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 89
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 89 (accept_3_2 31 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42
  89 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 89 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 89 (accept_3_2 28 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 89
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 42 89 (accept_3_2 25 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42
  89 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 42 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 89 (accept_3_2 22 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 42 89 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 89
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 89 (accept_3_2 19 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42
  89 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 42 89 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 89 (accept_3_2 16 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 89
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 89 (accept_3_2 13 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42
  89 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 89 (accept_3_2 10 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 89 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 89 (Polychromatic418967fa.accept_13_8_3_11_1_3467 8
  42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 89 (accept_3_2 7 42 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 89 (Polychromatic418967fa.accept_19_6_4_13_1_2329 6
  42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 89
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 89 (accept_3_2 4 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 89
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 89 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 89 (accept_3_2 1 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 89)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 89 (allA_succ_of_accept 40 41 89
  (accept_3_2 40 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 89
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 89 (accept_3_2 37 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 89 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 89 (Polychromatic418967fa.accept_10_5_1_9_1_791 35
  41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 89 (accept_3_2 34 41 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 89 (Polychromatic418967fa.accept_9_6_5_8_1_598 33
  41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 89
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 89 (accept_3_2 31 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  89 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 41 89 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 89 (accept_3_2 28 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 41 89 (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 41 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 89
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 89 (accept_3_2 25 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41
  89 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 41 89 (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 89 (accept_3_2 22 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 41 89 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 41 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 89 (accept_3_2 19 41 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 89 (Polychromatic418967fa.accept_7_4_6_5_1_141 18
  41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 89
  (Polychromatic418967fa.accept_13_4_2_11_1_733 17 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 89 (accept_3_2 16 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41
  89 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 41 89 (Polychromatic418967fa.accept_17_14_7_4_1_3476 14 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 89 (accept_3_2 13 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 41 89 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 89 (Polychromatic418967fa.accept_7_4_6_5_1_141 11
  41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 89 (accept_3_2 10 41 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 89 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9
  41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 89
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 89 (accept_3_2 7 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 89
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 89 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 89 (accept_3_2 4 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 89 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 41 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 41
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 89 (accept_3_2 1 41 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 89))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 89
  (allA_of_3_0 40 40 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 89 (allA_succ_of_accept 38 39 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 89 (accept_3_2 37 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39
  89 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 89 (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 89 (accept_3_2 34 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 89 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 39 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 32
  39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 89 (accept_3_2 31 39 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 89
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 89 (accept_3_2 28 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39
  89 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 89 (accept_3_2 25 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 89 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 23
  39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 89 (accept_3_2 22 39 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 89 (Polychromatic418967fa.accept_12_9_3_5_1_423 21
  39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 89 (accept_3_2 19 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39
  89 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 89 (Polychromatic418967fa.accept_27_17_12_8_1_3475 17 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 89 (accept_3_2 16 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 89 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 89 (accept_3_2 13 39 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 89 (Polychromatic418967fa.accept_15_12_9_14_1_2635
  12 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 89
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 89 (accept_3_2 10 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39
  89 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 89 (accept_3_2 7 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 39 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 39
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 89 (accept_3_2 4 39 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 89 (Polychromatic418967fa.accept_16_3_7_9_1_3474 3
  39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 89 (accept_3_2 1 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  89))))))))))))))))))))))))))))))))))))))) (allB_succ 38 89 (allA_succ_of_accept 37 38 89 (accept_3_2 37 38 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 38 89 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 38 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 38 89
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 38 89 (accept_3_2 34 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 38
  89 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 38 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 38 89 (accept_3_2 31 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 38 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 38 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 38 89 (Polychromatic418967fa.accept_7_1_3_5_1_33 29
  38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 89 (accept_3_2 28 38 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 89
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 26 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 89 (accept_3_2 25 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 38
  89 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 38 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 89 (accept_3_2 22 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 38 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 89 (Polychromatic418967fa.accept_12_8_2_5_1_844 20
  38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 38 89 (accept_3_2 19 38 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 38 89 (Polychromatic418967fa.accept_16_2_6_9_1_3473
  18 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 89
  (Polychromatic418967fa.accept_10_7_8_9_1_785 17 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 38 89 (accept_3_2 16 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38
  89 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 38 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 38 89 (accept_3_2 13 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 38 89 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 38 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 38 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 89 (accept_3_2 10 38 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 89
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 89 (accept_3_2 7 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38 89
  (Polychromatic418967fa.accept_9_6_2_8_1_592 6 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 89 (accept_3_2 4 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 38
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 89 (accept_3_2 1 38 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 89)))))))))))))))))))))))))))))))))))))) (allB_succ 37 89
  (allA_of_3_0 37 37 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 89 (allA_succ_of_accept 35 36 89
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 89 (accept_3_2 34 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36
  89 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 36 89 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 89 (accept_3_2 31 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 36 89 (Polychromatic418967fa.accept_13_4_10_11_1_1908 30 36 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 89 (Polychromatic418967fa.accept_8_5_4_1_1_111 29
  36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 89 (accept_3_2 28 36 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 89 (Polychromatic418967fa.accept_7_6_1_5_1_322 27
  36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 89
  (Polychromatic418967fa.accept_17_9_2_4_1_3472 26 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 89 (accept_3_2 25 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36
  89 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 89 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 89 (accept_3_2 22 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 89 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 89 (Polychromatic418967fa.accept_7_6_1_5_1_322 20
  36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 89 (accept_3_2 19 36 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 89 (Polychromatic418967fa.accept_7_4_1_5_1_540 18
  36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 89
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 89 (accept_3_2 16 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 36
  89 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 36 89 (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 89 (accept_3_2 13 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 36 89 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 36 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 89
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 89 (accept_3_2 10 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 36
  89 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 36 89 (Polychromatic418967fa.accept_13_8_10_11_1_2730 8 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 89 (accept_3_2 7 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 36 89 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 36 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 89 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 36
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 89 (accept_3_2 4 36 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 89 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 89
  (Polychromatic418967fa.accept_11_2_3_1_1_244 2 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 36 89 (accept_3_2 1 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  89)))))))))))))))))))))))))))))))))))) (allB_succ 35 89 (allA_succ_of_accept 34 35 89 (accept_3_2 34 35 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 89 (Polychromatic418967fa.accept_13_7_9_11_1_705 33 35 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 89
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 89 (accept_3_2 31 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35
  89 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 35 89 (Polychromatic418967fa.accept_19_10_16_13_1_3471 29 35 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 89 (accept_3_2 28 35 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 35 89 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 35 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 89 (accept_3_2 25 35 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 89 (Polychromatic418967fa.accept_10_4_5_9_1_1231
  24 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 89
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 89 (accept_3_2 22 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35
  89 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 89 (Polychromatic418967fa.accept_13_7_9_11_1_705 20 35 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 89 (accept_3_2 19 35 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 89 (Polychromatic418967fa.accept_15_2_5_14_1_61 17
  35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 89 (accept_3_2 16 35 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 89 (Polychromatic418967fa.accept_13_2_9_11_1_258
  15 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 89 (accept_3_2 13 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35
  89 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 89 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 35 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 89 (accept_3_2 10 35 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 89 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 35 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 89
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 8 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 89 (accept_3_2 7 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 89 (Polychromatic418967fa.accept_17_5_1_4_1_3460 5 35 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 89 (accept_3_2 4 35 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 89 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 35 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 89 (accept_3_2 1 35 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 89))))))))))))))))))))))))))))))))))) (allB_succ 34 89
  (allA_of_3_0 34 34 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 89 (allA_succ_of_accept 32 33 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 89 (accept_3_2 31 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33
  89 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 89 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 89 (accept_3_2 28 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 89 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 33 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 26
  33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 89 (accept_3_2 25 33 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 89 (Polychromatic418967fa.accept_10_4_3_9_1_1262
  24 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 89
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 89 (accept_3_2 22 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33
  89 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 89 (accept_3_2 19 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 89 (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 33 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 89 (Polychromatic418967fa.accept_13_4_7_11_1_1981
  17 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 89 (accept_3_2 16 33
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 89 (Polychromatic418967fa.accept_12_3_9_5_1_853
  15 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 89 (accept_3_2 13 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33
  89 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 89 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 89 (accept_3_2 10 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 89 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 33 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 89 (accept_3_2 7 33 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 89 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6
  33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 89
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 89 (accept_3_2 4 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 89
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 89 (accept_3_2 1 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 89))))))))))))))))))))))))))))))))) (allB_succ 32 89 (allA_succ_of_accept 31 32 89
  (accept_3_2 31 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 89
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 89 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 89 (accept_3_2 28 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 89 (Polychromatic418967fa.accept_12_2_8_5_1_408 26
  32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 89 (accept_3_2 25 32 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 89 (Polychromatic418967fa.accept_9_6_5_8_1_598 24
  32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 89
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 32 89 (accept_3_2 22 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 32
  89 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 32 89 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 89 (accept_3_2 19 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 32 89 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 32 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 89 (Polychromatic418967fa.accept_10_7_2_9_1_775 17
  32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 89 (accept_3_2 16 32 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 89
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 89 (accept_3_2 13 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 32
  89 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 32 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 89 (accept_3_2 10 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 32 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 89 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 32
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 89 (accept_3_2 7 32 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 89 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 32
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 89
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 89 (accept_3_2 4 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32 89
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 89 (accept_3_2 1 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 89)))))))))))))))))))))))))))))))) (allB_succ 31 89 (allA_of_3_0 31 31 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 30 89 (allA_succ_of_accept 29 30 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 89 (accept_3_2 28 30 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 30 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 89
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 89 (accept_3_2 25 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30
  89 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 89 (accept_3_2 22 30 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 89 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 30 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 20
  30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 89 (accept_3_2 19 30 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 89 (Polychromatic418967fa.accept_7_4_2_5_1_527 18
  30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 89
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 89 (accept_3_2 16 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 30
  89 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 30 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 30 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 89 (accept_3_2 13 30 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 30 89 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 30 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 89 (accept_3_2 10 30 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 89 (Polychromatic418967fa.accept_17_9_13_4_1_2408 9
  30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 89
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 8 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 89 (accept_3_2 7 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 89
  (Polychromatic418967fa.accept_9_6_3_8_1_595 6 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 89 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 30 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 89 (accept_3_2 4 30 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 30 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 30
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 89 (accept_3_2 1 30 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 89)))))))))))))))))))))))))))))) (allB_succ 29 89
  (allA_succ_of_accept 28 29 89 (accept_3_2 28 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29
  89 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 89 (Polychromatic418967fa.accept_17_9_12_4_1_3468 26 29 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 89 (accept_3_2 25 29 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 89 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 89 (accept_3_2 22 29 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 89 (Polychromatic418967fa.accept_9_3_2_8_1_108 21
  29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 89
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 89 (accept_3_2 19 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29
  89 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 29 89 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 89 (accept_3_2 16 29 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 29 89 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 29 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 89 (accept_3_2 13 29 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 89 (Polychromatic418967fa.accept_8_4_5_1_1_299 12
  29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 89
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 89 (accept_3_2 10 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29
  89 (Polychromatic418967fa.accept_17_9_12_4_1_3468 9 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 89 (Polychromatic418967fa.accept_13_8_3_11_1_3467 8 29 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 89 (accept_3_2 7 29 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 89 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 29 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 89 (accept_3_2 4 29 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 89 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 29
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 89
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 2 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 89 (accept_3_2 1 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  89))))))))))))))))))))))))))))) (allB_succ 28 89 (allA_of_3_0 28 28 89 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 27 89 (allA_succ_of_accept 26 27 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 89 (accept_3_2 25 27 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 89 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 27 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 89
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 89 (accept_3_2 22 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27
  89 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 89 (accept_3_2 19 27 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 89 (Polychromatic418967fa.accept_11_6_5_1_1_586 17
  27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 89 (accept_3_2 16 27 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 89 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 89 (accept_3_2 13 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27
  89 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 89 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 27 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 89 (accept_3_2 10 27 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 89 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 27 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 89 (accept_3_2 7 27 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 89
  (Polychromatic418967fa.accept_16_5_11_9_1_861 5 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 89 (accept_3_2 4 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 89
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 89 (accept_3_2 1 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 89))))))))))))))))))))))))))) (allB_succ 26 89 (allA_succ_of_accept 25 26 89 (accept_3_2 25 26 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 89 (Polychromatic418967fa.accept_14_10_12_5_1_3466
  24 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 89
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 89 (accept_3_2 22 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 26
  89 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 26 89 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 26 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 89 (accept_3_2 19 26 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 26 89 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 26 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 89 (Polychromatic418967fa.accept_14_3_12_5_1_153
  17 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 89 (accept_3_2 16 26
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 89 (Polychromatic418967fa.accept_4_3_2_1_1_50
  15 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 89
  (Polychromatic418967fa.accept_17_14_9_4_1_3465 14 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 89 (accept_3_2 13 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26
  89 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 89 (accept_3_2 10 26 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 89
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 89 (accept_3_2 7 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 89
  (Polychromatic418967fa.accept_19_6_7_13_1_2289 6 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 89 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 26 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 89 (accept_3_2 4 26 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 89 (Polychromatic418967fa.accept_17_2_9_4_1_3463 2
  26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 89 (accept_3_2 1 26 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 89)))))))))))))))))))))))))) (allB_succ 25 89 (allA_of_3_0 25 25
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 89 (allA_succ_of_accept 23 24 89
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 89 (accept_3_2 22 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24
  89 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 89 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 24 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 89 (accept_3_2 19 24 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 89 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 24 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 89 (Polychromatic418967fa.accept_16_1_8_9_1_3462
  17 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 89 (accept_3_2 16 24
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 89 (Polychromatic418967fa.accept_7_1_3_5_1_33
  15 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 89
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 89 (accept_3_2 13 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24
  89 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 89 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 89 (accept_3_2 10 24 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 89 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 24
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 89 (accept_3_2 7 24 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 89 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6
  24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 89
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 89 (accept_3_2 4 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 89
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 89 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 24 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 89 (accept_3_2 1 24 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 89)))))))))))))))))))))))) (allB_succ 23 89 (allA_succ_of_accept 22 23 89 (accept_3_2 22 23
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 89 (Polychromatic418967fa.accept_9_3_5_8_1_99
  21 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 89
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 89 (accept_3_2 19 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 23
  89 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 23 89 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 23 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 89 (accept_3_2 16 23 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 23 89 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 23 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 89 (accept_3_2 13 23 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 89 (Polychromatic418967fa.accept_9_3_5_8_1_99 12
  23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 89
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 89 (accept_3_2 10 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23
  89 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 89 (Polychromatic418967fa.accept_13_8_10_11_1_2730 8 23 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 89 (accept_3_2 7 23 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 89 (Polychromatic418967fa.accept_15_5_8_14_1_432 5
  23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 89 (accept_3_2 4 23 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 89 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 23
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 89 (accept_3_2 1 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  89))))))))))))))))))))))) (allB_succ 22 89 (allA_of_3_0 22 22 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  21 89 (allA_succ_of_accept 20 21 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 89 (accept_3_2 19 21 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 89 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 21 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 89 (Polychromatic418967fa.accept_13_4_8_11_1_1937
  17 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 89 (accept_3_2 16 21
  89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 89 (Polychromatic418967fa.accept_9_6_3_8_1_595
  15 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 89 (accept_3_2 13 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21
  89 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 21 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 89 (accept_3_2 10 21 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 89 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 21 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 89 (accept_3_2 7 21 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 89 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 89
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 89 (accept_3_2 4 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 89
  (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 89 (accept_3_2 1 21 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 21 89))))))))))))))))))))) (allB_succ 20 89 (allA_succ_of_accept 19 20 89 (accept_3_2 19 20 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 89 (Polychromatic418967fa.accept_7_4_6_5_1_141 18
  20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 20 89
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 17 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 20 89 (accept_3_2 16 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 20
  89 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 20 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 20 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 89 (accept_3_2 13 20 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 20 89 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 20 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 89 (Polychromatic418967fa.accept_7_4_6_5_1_141 11
  20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 89 (accept_3_2 10 20 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 89
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 89 (accept_3_2 7 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 89
  (Polychromatic418967fa.accept_9_6_2_8_1_592 6 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 89 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 20 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 89 (accept_3_2 4 20 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 89 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 89 (accept_3_2 1 20 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 89)))))))))))))))))))) (allB_succ 19 89 (allA_of_3_0 19 19 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 18 89 (allA_succ_of_accept 17 18 89
  (Polychromatic418967fa.accept_10_7_8_9_1_785 17 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 18 89 (accept_3_2 16 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18
  89 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 18 89 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 18 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 89 (accept_3_2 13 18 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 18 89 (Polychromatic418967fa.accept_16_12_2_9_1_3461 12 18 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 89 (accept_3_2 10 18 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 89
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 89 (accept_3_2 7 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 89
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 89 (Polychromatic418967fa.accept_17_5_1_4_1_3460 5 18 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 89 (accept_3_2 4 18 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 89 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 18
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 89 (accept_3_2 1 18 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 89)))))))))))))))))) (allB_succ 17 89 (allA_succ_of_accept 16 17
  89 (accept_3_2 16 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 89
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 89 (Polychromatic418967fa.accept_21_14_17_5_1_3459 14 17 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 89 (accept_3_2 13 17 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 89 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 17 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 89
  (Polychromatic418967fa.accept_19_11_17_13_1_3458 11 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 89 (accept_3_2 10 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17
  89 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 89 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 17 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 89 (accept_3_2 7 17 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 89 (Polychromatic418967fa.accept_13_6_4_11_1_282 6 17 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 89 (Polychromatic418967fa.accept_11_5_6_1_1_988 5
  17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 89 (accept_3_2 4 17 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 89 (Polychromatic418967fa.accept_15_3_2_14_1_1713 3
  17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 89
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 89 (accept_3_2 1 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  89))))))))))))))))) (allB_succ 16 89 (allA_of_3_0 16 16 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 89
  (allA_succ_of_accept 14 15 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 89 (accept_3_2 13 15 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 89 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 15 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 89 (Polychromatic418967fa.accept_7_4_1_5_1_540 11
  15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 89 (accept_3_2 10 15 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 89 (Polychromatic418967fa.accept_12_9_3_5_1_423 9
  15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 89
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 89 (accept_3_2 7 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 89 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 15 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 89 (accept_3_2 4 15 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 89 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 89 (accept_3_2 1 15 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 89))))))))))))))) (allB_succ 14 89 (allA_succ_of_accept 13 14 89
  (accept_3_2 13 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 89
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 89 (accept_3_2 10 14 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 89 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 89 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8
  14 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 89 (accept_3_2 7 14 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 89 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 14
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 89
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 89 (accept_3_2 4 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 89
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 89 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 14 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 89 (accept_3_2 1 14 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 89)))))))))))))) (allB_succ 13 89 (allA_of_3_0 13 13 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 89 (allA_succ_of_accept 11 12 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 12 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 89 (accept_3_2 10 12 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 89 (Polychromatic418967fa.accept_15_9_12_14_1_963 9
  12 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 89
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 8 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 89 (accept_3_2 7 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 89
  (Polychromatic418967fa.accept_9_6_3_8_1_595 6 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 89 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 89 (accept_3_2 4 12 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 89 (Polychromatic418967fa.accept_14_3_12_5_1_153 3 12 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 89 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 12
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 89 (accept_3_2 1 12 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 89)))))))))))) (allB_succ 11 89 (allA_succ_of_accept 10 11 89
  (accept_3_2 10 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 89
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 89 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 11 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 89 (accept_3_2 7 11 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 89 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 89 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 11
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 89 (accept_3_2 4 11 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 89 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 11
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 89 (accept_3_2 1 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 89)))))))))))
  (allB_succ 10 89 (allA_of_3_0 10 10 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 89 (allA_succ_of_accept 8
  9 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 89 (accept_3_2 7 9 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 89
  (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 9 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 89 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 9 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 89 (accept_3_2 4 9 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 89 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 89 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 89 (accept_3_2 1 9 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 9 89))))))))) (allB_succ 8 89 (allA_succ_of_accept 7 8 89 (accept_3_2 7 8 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 89 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 8
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 89
  (Polychromatic418967fa.accept_15_5_8_14_1_432 5 8 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 89 (accept_3_2 4 8 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 89
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 89 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 8 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 89 (accept_3_2 1 8 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 89)))))))) (allB_succ 7 89 (allA_of_3_0 7 7 89 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 89 (allA_succ_of_accept 5 6 89 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 89 (accept_3_2 4 6 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 6 89 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 89 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 6 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 89 (accept_3_2 1 6 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 89)))))) (allB_succ 5 89 (allA_succ_of_accept 4 5 89 (accept_3_2 4 5 89
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 89 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 5 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 89
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 89 (accept_3_2 1 5 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 89))))) (allB_succ
  4 89 (allA_of_3_0 4 4 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 89 (allA_succ_of_accept 2 3 89
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 89 (accept_3_2 1 3 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 89))) (allB_succ 2
  89 (allA_succ_of_accept 1 2 89 (accept_3_2 1 2 89 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 89)) (allB_two
  89)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


