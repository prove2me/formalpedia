-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch85
-- name    : Polychromatic418967fa_Branch85
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:08:53.38911+00:00
-- url     : https://prove2.me/theorems/a6f50cc6-d2bc-4453-9b22-77934e3cd316
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

def Polychromatic418967fa.branch_85 : allB 85 85 :=
  allB_succ' 2 84 85 (Eq.refl Bool.true) (allA_succ_of_accept 1 84 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 85)) (allB_succ' 3 83 85 (Eq.refl Bool.true)
  (allA_of_3_1 3 83 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 82 85 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 82 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 85 (accept_3_3 2 82 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 85 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 82 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 85)))) (allB_succ' 5 81 85 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 81 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 85 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 85 (accept_3_3 2 81 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 85 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 81 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 85))))) (allB_succ' 6 80 85 (Eq.refl
  Bool.true) (allA_of_3_1 6 80 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 79 85 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 79 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 85 (accept_3_3 5 79 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 79 85 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 79 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 79 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 85 (accept_3_3 2 79 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 85 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 79 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 85))))))) (allB_succ' 8 78 85 (Eq.refl
  Bool.true) (allA_succ_of_accept 7 78 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 85 (Polychromatic418967fa.accept_15_6_3_10_1_2341 6
  78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 85 (accept_3_3 5 78 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 85 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4
  78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 85 (accept_3_3 2 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 85
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 85)))))))) (allB_succ' 9 77 85 (Eq.refl Bool.true) (allA_of_3_1 9 77 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 10 76 85 (Eq.refl Bool.true) (allA_succ_of_accept 9 76 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 85 (accept_3_3 8 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 85
  (Polychromatic418967fa.accept_14_7_6_1_1_1656 7 76 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 85 (Polychromatic418967fa.accept_15_6_1_10_1_1549 6 76 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 85 (accept_3_3 5 76 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 85 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 76 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 85 (accept_3_3 2 76 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 76
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 85)))))))))) (allB_succ' 11 75 85
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 75 85 5 2 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 75 85 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 75 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 85 (accept_3_3 8 75 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 85 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 75 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 85
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 75 85 5 1 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 85 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 85 (accept_3_3 2 75 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 85 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 75 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 85))))))))))) (allB_succ' 12 74 85 (Eq.refl
  Bool.true) (allA_of_3_1 12 74 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 73 85 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 73 85 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 85 (accept_3_3 11 73 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 73 85 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 73 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 85 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 73
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 85 (accept_3_3 8 73 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 85 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 85
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 85 (accept_3_3 5 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73 85
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 73 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 85 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 73 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 85 (accept_3_3 2 73 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 85 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 73 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 85))))))))))))) (allB_succ' 14 72 85 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 72 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 85 (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 72 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 85 (accept_3_3 11 72 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 10
  72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 85
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 72 85 (accept_3_3 8 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 85
  (Polychromatic418967fa.accept_10_7_2_5_1_298 7 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 72 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 72 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 85 (accept_3_3 5 72 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 72 85 (Polychromatic418967fa.accept_16_4_8_5_1_3317 4 72 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 85 (accept_3_3 2 72 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 85 (Polychromatic418967fa.accept_25_1_22_10_1_3339
  1 72 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 85)))))))))))))) (allB_succ' 15 71
  85 (Eq.refl Bool.true) (allA_of_3_1 15 71 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 70 85 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 70 85 5 3 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 70 85 (accept_3_3 14 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 70 85 (Polychromatic418967fa.accept_20_13_10_5_1_3338 13 70 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 85 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 70 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 85 (accept_3_3 11 70 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 85 5 2 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 85 (accept_3_3 8 70 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 85
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 70 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 70 85 5 1 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 70 85 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 70 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 85 (accept_3_3 2 70 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 85 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 85)))))))))))))))) (allB_succ' 17 69 85
  (Eq.refl Bool.true) (allA_succ_of_accept 16 69 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 85
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 85 (accept_3_3 14 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69
  85 (Polychromatic418967fa.accept_25_13_19_10_1_3337 13 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 85 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 85 (accept_3_3 11 69 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 85
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 85 (accept_3_3 8 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 85
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 69 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 85 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 69 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 85 (accept_3_3 5 69 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 85 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 69
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 85 (accept_3_3 2 69 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 85 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 69
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 85))))))))))))))))) (allB_succ' 18 68 85
  (Eq.refl Bool.true) (allA_of_3_1 18 68 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 67 85 (Eq.refl
  Bool.true) (allA_succ_of_accept 18 67 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 85 (accept_3_3 17 67 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 85 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 67 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 85
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 85 (accept_3_3 14 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67
  85 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 67 85 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 85 (accept_3_3 11 67 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 67 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 85 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9
  67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 85 (accept_3_3 8 67 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 85 (Polychromatic418967fa.accept_19_7_10_9_1_2162 7
  67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 85
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 85 (accept_3_3 5 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 85
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 67 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 85 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 85 (accept_3_3 2 67 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 85 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 67 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 85))))))))))))))))))) (allB_succ' 20 66 85 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 85 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 66 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 85 (accept_3_3 17 66 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 85 (Polychromatic418967fa.accept_7_2_3_1_1_10 16
  66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 85 (accept_3_3 14 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66
  85 (Polychromatic418967fa.accept_16_13_2_5_1_3336 13 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 85 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 66 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 85 (accept_3_3 11 66 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 85 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 66 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 85
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 85 (accept_3_3 8 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 85 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 66 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 85 (accept_3_3 5 66 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 85 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 66 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 85 (accept_3_3 2 66 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 85 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 66
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 85)))))))))))))))))))) (allB_succ' 21 65
  85 (Eq.refl Bool.true) (allA_of_3_1 21 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 64 85 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 64 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 85 (accept_3_3 20 64 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 85 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 64 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 85
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 85 (accept_3_3 17 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64
  85 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 64 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 85 (accept_3_3 14 64 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 64 85 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 64 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 85 (Polychromatic418967fa.accept_9_3_1_4_1_216 12
  64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 85 (accept_3_3 11 64 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 85 (Polychromatic418967fa.accept_11_10_9_8_1_1974
  10 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 85 (accept_3_3 8 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 85
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 85 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 64 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 85 (accept_3_3 5 64 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 85 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 64 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 85 (accept_3_3 2 64 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 85 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1
  64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 85)))))))))))))))))))))) (allB_succ'
  23 63 85 (Eq.refl Bool.true) (allA_succ_of_accept 22 63 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 85
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 85 (accept_3_3 20 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63
  85 (Polychromatic418967fa.accept_25_19_13_10_1_3335 19 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 85 (accept_3_3 17 63 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 85
  (Polychromatic418967fa.accept_19_15_6_9_1_3334 15 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 85 (accept_3_3 14 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63
  85 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 85 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 63 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 85 (accept_3_3 11 63 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 85
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 85 (accept_3_3 8 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 85
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 85 (accept_3_3 5 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 85 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 63 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 85 (accept_3_3 2 63 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 85 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 63 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 85))))))))))))))))))))))) (allB_succ' 24 62
  85 (Eq.refl Bool.true) (allA_of_3_1 24 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 61 85 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 61 85 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 85 (accept_3_3 23 61 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 85 (Polychromatic418967fa.accept_15_7_1_10_1_305 22 61 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 85
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 61 85 (accept_3_3 20 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61
  85 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 61 85 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 61 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 85 (accept_3_3 17 61 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 61 85 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 61 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 85 (Polychromatic418967fa.accept_9_6_7_4_1_212 15
  61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 85 (accept_3_3 14 61 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 85 (Polychromatic418967fa.accept_7_6_5_1_1_416 13
  61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 85
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 85 (accept_3_3 11 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61
  85 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 61 85 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 61 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 85 (accept_3_3 8 61 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 61 85 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 61 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 85 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 61
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 85 (accept_3_3 5 61 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 85 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 61
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 85
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 85 (accept_3_3 2 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 85
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 61 85))))))))))))))))))))))))) (allB_succ' 26 60 85 (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 85 5 5 12 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 60 85
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 85 (accept_3_3 23 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60
  85 (Polychromatic418967fa.accept_13_9_8_7_1_1073 22 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 60 85 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 85 5 4 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 85 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 85
  (Polychromatic418967fa.accept_19_18_3_9_1_3333 18 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 85 (accept_3_3 17 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60
  85 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 60 85 5 3 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 60 85 (accept_3_3 14 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60
  85 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 60 85 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 60 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 85 (accept_3_3 11 60 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 85 5 2 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 60 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 60 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 85 (accept_3_3 8 60 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 60 85 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 85 (Polychromatic418967fa.accept_19_6_3_9_1_3332 6
  60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 60 85 5 1 12 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 85
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 85 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 85 (accept_3_3 2 60 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 60 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 85)))))))))))))))))))))))))) (allB_succ' 27 59 85 (Eq.refl
  Bool.true) (allA_of_3_1 27 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 58 85 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 58 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 85 (accept_3_3 26 58 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 58 85 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 58 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 24
  58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 85 (accept_3_3 23 58 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 85 (Polychromatic418967fa.accept_10_2_8_5_1_587 22
  58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 85 (accept_3_3 20 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 58
  85 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 58 85 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 58 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 85 (accept_3_3 17 58 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 58 85 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 58 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 85 (accept_3_3 14 58 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 85
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 85 (accept_3_3 11 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58
  85 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 58 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 85 (accept_3_3 8 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 58 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 58 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 85 (accept_3_3 5 58 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 85 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 58 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 58 85 (accept_3_3 2 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 85
  (Polychromatic418967fa.accept_13_1_6_7_1_550 1 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 85)))))))))))))))))))))))))))) (allB_succ' 29 57 85 (Eq.refl Bool.true) (allA_succ_of_accept 28 57 85
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 57 85 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 85 (accept_3_3 26 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 57 85 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 57 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 85 (Polychromatic418967fa.accept_9_6_3_4_1_477 24
  57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 85 (accept_3_3 23 57 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 85
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 85 (accept_3_3 20 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57
  85 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 85 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 85 (accept_3_3 17 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 85 (Polychromatic418967fa.accept_9_6_3_4_1_477 15
  57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 85 (accept_3_3 14 57 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 85 (Polychromatic418967fa.accept_10_3_7_5_1_288 13
  57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 85
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 85 (accept_3_3 11 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57
  85 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 57 85 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 85 (accept_3_3 8 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 57 85 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 57 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 85 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 57
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 85 (accept_3_3 5 57 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 85
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 85 (accept_3_3 2 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 85
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 85))))))))))))))))))))))))))))) (allB_succ' 30 56 85 (Eq.refl Bool.true) (allA_of_3_1 30 56 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 55 85 (Eq.refl Bool.true) (allA_succ_of_gcd 30 55 85 5 6 11 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 85 (accept_3_3 29 55
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 85
  (Polychromatic418967fa.accept_16_12_7_5_1_1412 28 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 55 85 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 85 (accept_3_3 26 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 55 85 5 5 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 55 85 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 85 (accept_3_3 23 55 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 85
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 55 85 5 4 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 55 85 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 85 (accept_3_3 17 55 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 85 (Polychromatic418967fa.accept_7_2_6_1_1_73 16
  55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 85 5 3 11 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 85 (accept_3_3 14 55
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 85
  (Polychromatic418967fa.accept_19_13_17_9_1_3312 13 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 55 85 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 85 (accept_3_3 11 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 55 85 5 2 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 55 85 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 55 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 85 (accept_3_3 8 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 55 85 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 85 5 1 11 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 85
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 85 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 85 (accept_3_3 2 55 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 85 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 55 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 85))))))))))))))))))))))))))))))) (allB_succ' 32 54 85 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 54 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 85 (Polychromatic418967fa.accept_20_10_14_5_1_3331
  30 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 85 (accept_3_3 29 54
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 85
  (Polychromatic418967fa.accept_20_8_14_5_1_2119 28 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 54 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 85 (accept_3_3 26 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 54 85 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 54 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 85 (Polychromatic418967fa.accept_7_3_5_1_1_72 24
  54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 85 (accept_3_3 23 54 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 85 (Polychromatic418967fa.accept_13_9_2_7_1_1083
  22 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 85
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 54 85 (accept_3_3 20 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54
  85 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 54 85 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 85 (accept_3_3 17 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 54 85 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 54 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 85 (accept_3_3 14 54 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 85 (Polychromatic418967fa.accept_7_6_5_1_1_416 13
  54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 85
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 85 (accept_3_3 11 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54
  85 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 54 85 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 85 (accept_3_3 8 54 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 54 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 85 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 54
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 85 (accept_3_3 5 54 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 85 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 54
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 54 85 (accept_3_3 2 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 85
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 85)))))))))))))))))))))))))))))))) (allB_succ' 33 53 85 (Eq.refl Bool.true) (allA_of_3_1 33 53 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 52 85 (Eq.refl Bool.true) (allA_succ_of_accept 33 52 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 85 (accept_3_3 32 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 52
  85 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 52 85 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 85 (accept_3_3 29 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 52 85 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 52 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 85 (accept_3_3 26 52 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 85 (Polychromatic418967fa.accept_7_4_3_1_1_87 25
  52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 85
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 85 (accept_3_3 23 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52
  85 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 85 (accept_3_3 20 52 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 85 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 52 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 85
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 85 (accept_3_3 17 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52
  85 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 52 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 85 (accept_3_3 14 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 52 85 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 52 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 85 (Polychromatic418967fa.accept_7_5_3_1_1_424 12
  52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 85 (accept_3_3 11 52 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 85 (Polychromatic418967fa.accept_9_1_7_4_1_52 10
  52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 85 (accept_3_3 8 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 85
  (Polychromatic418967fa.accept_10_7_2_5_1_298 7 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 52 85 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 85 (accept_3_3 5 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 52 85 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 52 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 85 (accept_3_3 2 52 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 52
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 85))))))))))))))))))))))))))))))))))
  (allB_succ' 35 51 85 (Eq.refl Bool.true) (allA_succ_of_gcd 34 51 85 17 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 51 85 (Polychromatic418967fa.accept_12_9_3_1_1_303 33
  51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 85 (accept_3_3 32 51 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 31
  51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 85
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 85 (accept_3_3 29 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51
  85 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 51 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 85 (accept_3_3 26 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 51 85 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 51 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 24
  51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 85 (accept_3_3 23 51 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 85
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 85 (accept_3_3 20 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51
  85 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 51 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 51 85 17 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 51 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 85
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 85 (accept_3_3 14 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51
  85 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 51 85 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 85 (accept_3_3 11 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 85 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 85 (accept_3_3 8 51 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 85 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 51
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 85
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 85 (accept_3_3 5 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 85
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 85 (accept_3_3 2 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 85 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 51 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 85))))))))))))))))))))))))))))))))))) (allB_succ' 36 50 85
  (Eq.refl Bool.true) (allA_of_3_1 36 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 49 85 (Eq.refl
  Bool.true) (allA_succ_of_accept 36 49 85 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 85 (accept_3_3 35 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 85 (Polychromatic418967fa.accept_10_4_9_5_1_84 34 49 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 85
  (Polychromatic418967fa.accept_19_14_11_9_1_3330 33 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 85 (accept_3_3 32 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49
  85 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 49 85 (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 85 (accept_3_3 29 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 49 85 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 85 (Polychromatic418967fa.accept_14_13_7_1_1_1618
  27 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 85 (accept_3_3 26 49
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 85 (Polychromatic418967fa.accept_11_3_5_8_1_458
  25 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 85
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 85 (accept_3_3 23 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49
  85 (Polychromatic418967fa.accept_14_8_7_1_1_1615 22 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 49 85 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 85 (accept_3_3 20 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 49 85 (Polychromatic418967fa.accept_21_19_7_1_1_3329 19 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 85
  (Polychromatic418967fa.accept_25_18_24_10_1_3328 18 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 85 (accept_3_3 17 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49
  85 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 49 85 (Polychromatic418967fa.accept_16_15_1_5_1_2265 15 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 85 (accept_3_3 14 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 49 85 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 85 (Polychromatic418967fa.accept_8_4_1_5_1_186 12
  49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 85 (accept_3_3 11 49 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 85 (Polychromatic418967fa.accept_20_10_9_5_1_3327
  10 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 85
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 85 (accept_3_3 8 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 85
  (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 85 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 85 (accept_3_3 5 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 85 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 85 (Polychromatic418967fa.accept_11_3_5_8_1_458 3
  49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 85 (accept_3_3 2 49 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 85 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 49
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 85)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 48 85 (Eq.refl Bool.true) (allA_succ_of_accept 37 48 85 (Polychromatic418967fa.accept_7_2_6_1_1_73 37
  48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 85
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 85 (accept_3_3 35 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48
  85 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 85 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 85 (accept_3_3 32 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 85 (Polychromatic418967fa.accept_19_12_10_9_1_3326 31 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 85 (Polychromatic418967fa.accept_7_2_6_1_1_73 30
  48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 85 (accept_3_3 29 48 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 85 (Polychromatic418967fa.accept_9_1_3_4_1_47 28
  48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 85
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 48 85 (accept_3_3 26 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48
  85 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 48 85 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 85 (accept_3_3 23 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 48 85 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 85 (Polychromatic418967fa.accept_13_8_9_7_1_530 21
  48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 85 (accept_3_3 20 48 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 85 (Polychromatic418967fa.accept_7_5_6_1_1_407 19
  48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 85
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 85 (accept_3_3 17 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48
  85 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 48 85 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 85 (accept_3_3 14 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 48 85 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 85 (Polychromatic418967fa.accept_7_5_6_1_1_407 12
  48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 85 (accept_3_3 11 48 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 85 (Polychromatic418967fa.accept_9_1_3_4_1_47 10
  48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 85
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 48 85 (accept_3_3 8 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 85
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 48 85 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 85 (accept_3_3 5 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 48 85 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48 85 (Polychromatic418967fa.accept_10_3_8_5_1_606 3
  48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 85 (accept_3_3 2 48 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 85 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 85))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 47 85 (Eq.refl Bool.true) (allA_of_3_1 39 47 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40
  46 85 (Eq.refl Bool.true) (allA_succ_of_accept 39 46 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 85 (accept_3_3 38 46 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 46 85 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 46 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 85
  (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 46 85 (accept_3_3 35 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46
  85 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 46 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 85 (accept_3_3 32 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 46 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 85 (Polychromatic418967fa.accept_9_3_1_4_1_216 30
  46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 85 (accept_3_3 29 46 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 85 (Polychromatic418967fa.accept_12_4_10_1_1_706
  28 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 85 (accept_3_3 26 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 46
  85 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 46 85 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 85 (accept_3_3 23 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 46 85 (Polychromatic418967fa.accept_15_7_1_10_1_305 22 46 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 85 (accept_3_3 20 46 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 46 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 19
  46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 85
  (Polychromatic418967fa.accept_19_18_8_9_1_3325 18 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 46 85 (accept_3_3 17 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46
  85 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 46 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 85 (accept_3_3 14 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 46 85 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 46 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 85 (Polychromatic418967fa.accept_7_5_4_1_1_412 12
  46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 85 (accept_3_3 11 46 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 85 (Polychromatic418967fa.accept_7_3_4_1_1_71 10
  46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 85 (accept_3_3 8 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 85 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 85 (accept_3_3 5 46 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 85 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 46 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 85 (accept_3_3 2 46 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 85 (Polychromatic418967fa.accept_10_1_6_5_1_304 1
  46 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  85)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 45 85 (Eq.refl Bool.true) (allA_succ_of_gcd 40 45 85 5 8 9
  17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 45 85
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 85 (accept_3_3 38 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45
  85 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 45 85 (Polychromatic418967fa.accept_19_17_7_9_1_3324 36 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 85 5 7 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 85
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 85 (accept_3_3 32 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45
  85 (Polychromatic418967fa.accept_21_10_3_1_1_3323 31 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 45 85 5 6 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 45 85 (accept_3_3 29 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 85 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 45 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 85 (accept_3_3 26 45 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 85 5 5 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 45 85 (Polychromatic418967fa.accept_16_8_13_5_1_1395
  24 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 85 (accept_3_3 23 45
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 85 (Polychromatic418967fa.accept_6_4_3_1_1_57
  22 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 85
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 45 85 5 4 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 85 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 85 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 85 (accept_3_3 17 45 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 85 5 3 9 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 85 (accept_3_3 14 45
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 85
  (Polychromatic418967fa.accept_19_13_7_9_1_3322 13 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 85 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 85 (accept_3_3 11 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 45 85 5 2 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 45 85 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 85 (accept_3_3 8 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 45 85 (Polychromatic418967fa.accept_21_7_3_1_1_3321 7 45 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 85 (Polychromatic418967fa.accept_18_6_9_13_1_3320 6
  45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 45 85 5 1 9 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 85
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 85 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 85 (accept_3_3 2 45 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 85 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 45 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 85))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 44 85
  (Eq.refl Bool.true) (allA_of_3_1 42 44 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 85
  (allA_succ_of_accept 42 43 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 85 (accept_3_3 41 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 85 (Polychromatic418967fa.accept_16_8_11_5_1_3319 40 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 85 (Polychromatic418967fa.accept_9_3_7_4_1_53 39
  43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 85 (accept_3_3 38 43 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 85 (Polychromatic418967fa.accept_9_1_7_4_1_52 37
  43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 85
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 85 (accept_3_3 35 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43
  85 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 43 85 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 85 (accept_3_3 32 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 43 85 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 85 (accept_3_3 29 43 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 85 (Polychromatic418967fa.accept_9_1_7_4_1_52 28
  43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 85
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 85 (accept_3_3 26 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43
  85 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 85 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 85 (accept_3_3 23 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 85
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 85 (accept_3_3 20 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43
  85 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 43 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 85 (accept_3_3 17 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 43 85 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 85 (Polychromatic418967fa.accept_9_6_7_4_1_212 15
  43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 85 (accept_3_3 14 43 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 85 (Polychromatic418967fa.accept_19_13_5_9_1_3318
  13 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 85
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 85 (accept_3_3 11 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43
  85 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 43 85 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 85 (accept_3_3 8 43 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 43 85 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 85 (accept_3_3 5 43 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 85 (Polychromatic418967fa.accept_15_4_13_10_1_1508
  4 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 85
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 85 (accept_3_3 2 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 85
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 85))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 85 (allA_succ_of_accept 41 42 85 (accept_3_3
  41 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 85
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 40 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 42 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 85 (accept_3_3 38 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 42 85 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 85 (Polychromatic418967fa.accept_13_10_3_7_1_2517
  36 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 85 (accept_3_3 35 42
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 85 (Polychromatic418967fa.accept_9_7_6_4_1_483
  34 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 85
  (Polychromatic418967fa.accept_10_3_2_5_1_295 33 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 42 85 (accept_3_3 32 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42
  85 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 42 85 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 85 (accept_3_3 29 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 42 85 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 42 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 85 (accept_3_3 26 42 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 85 (Polychromatic418967fa.accept_9_7_6_4_1_483 25
  42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 85
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 85 (accept_3_3 23 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42
  85 (Polychromatic418967fa.accept_13_9_3_7_1_1065 22 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 42 85 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 85 (accept_3_3 20 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 42 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 85 (Polychromatic418967fa.accept_10_8_2_5_1_596 18
  42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 85 (accept_3_3 17 42 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 85 (Polychromatic418967fa.accept_9_7_6_4_1_483 16
  42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 42 85 (accept_3_3 14 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42
  85 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 42 85 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 85 (accept_3_3 11 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 42 85 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 42 85 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9
  42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 85 (accept_3_3 8 42 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 85
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 85 (accept_3_3 5 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 85
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 42 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 85 (accept_3_3 2 42 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 85 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 85)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 85
  (allA_of_3_1 41 41 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 85 (allA_succ_of_accept 39 40 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 85 (accept_3_3 38 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 40
  85 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 40 85 (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 40 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 40 85 5 7 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 40 85 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 40 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 85 (accept_3_3 32 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 40
  85 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 85 5 6 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 85 (accept_3_3 29 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 40
  85 (Polychromatic418967fa.accept_16_12_8_5_1_3316 28 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 40 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 85 (accept_3_3 26 40 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40 85 5 5 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 40 85 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 85 (accept_3_3 23 40 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 85 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 40 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 85 5 4 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 85 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 40 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 85 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 40 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 85 (accept_3_3 17 40 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 85 (Polychromatic418967fa.accept_13_3_1_7_1_1706
  16 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 40 85 5 3 8 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 40 85 (accept_3_3 14 40
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 85 (Polychromatic418967fa.accept_7_6_5_1_1_416
  13 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 85
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 85 (accept_3_3 11 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 85
  5 2 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 85 (accept_3_3 8 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 85
  (Polychromatic418967fa.accept_18_7_4_13_1_3315 7 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 85 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 40 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 40 85 5 1 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 40 85 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 40 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 85 (accept_3_3 2 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 85
  (Polychromatic418967fa.accept_19_1_2_9_1_3314 1 40 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 85)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 85 (allA_succ_of_accept 38 39 85 (accept_3_3 38
  39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 85
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 85 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 85 (accept_3_3 35 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 85 (Polychromatic418967fa.accept_7_5_4_1_1_412 33
  39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 85 (accept_3_3 32 39 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 85 (Polychromatic418967fa.accept_7_3_4_1_1_71 31
  39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 85
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 85 (accept_3_3 29 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39
  85 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 39 85 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 85 (accept_3_3 26 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 39 85 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 39 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 85 (Polychromatic418967fa.accept_7_3_4_1_1_71 24
  39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 85 (accept_3_3 23 39 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 85
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 85 (accept_3_3 20 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39
  85 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 85 (accept_3_3 17 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 39 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 85 (Polychromatic418967fa.accept_9_6_3_4_1_477 15
  39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 85 (accept_3_3 14 39 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 85 (Polychromatic418967fa.accept_20_13_19_5_1_1012
  13 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 85
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 85 (accept_3_3 11 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39
  85 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 39 85 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 85 (accept_3_3 8 39 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 39 85 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 39 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 85 (accept_3_3 5 39 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 85
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 39 85 (accept_3_3 2 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 85
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 39 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 39 85))))))))))))))))))))))))))))))))))))))) (allB_succ 38 85 (allA_of_3_1 38 38 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 37 85 (allA_succ_of_accept 36 37 85 (Polychromatic418967fa.accept_14_8_9_1_1_3313 36
  37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 85 (accept_3_3 35 37 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 34
  37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 85
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 85 (accept_3_3 32 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37
  85 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 85 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 85 (accept_3_3 29 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 85 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 37 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 27
  37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 85 (accept_3_3 26 37 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 85 (Polychromatic418967fa.accept_9_7_1_4_1_217 25
  37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 85
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 85 (accept_3_3 23 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37
  85 (Polychromatic418967fa.accept_10_2_7_5_1_605 22 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 37 85 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 85 (accept_3_3 20 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 37 85 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 37 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 85 (Polychromatic418967fa.accept_10_8_7_5_1_602 18
  37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 85 (accept_3_3 17 37 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 85 (Polychromatic418967fa.accept_9_7_1_4_1_217 16
  37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 85
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 85 (accept_3_3 14 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37
  85 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 85 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 85 (accept_3_3 11 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 37 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 85 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9
  37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 85 (accept_3_3 8 37 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 85 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 85
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 85 (accept_3_3 5 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 85
  (Polychromatic418967fa.accept_13_4_11_7_1_558 4 37 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 85 (accept_3_3 2 37 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 85 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 37 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 85))))))))))))))))))))))))))))))))))))) (allB_succ 36 85
  (allA_succ_of_accept 35 36 85 (accept_3_3 35 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36
  85 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 36 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 85 (accept_3_3 32 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 36 85 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 36 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 85 (Polychromatic418967fa.accept_13_4_10_7_1_1701
  30 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 85 (accept_3_3 29 36
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 85 (Polychromatic418967fa.accept_11_6_3_8_1_843
  28 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 85
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 36 85 (accept_3_3 26 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36
  85 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 36 85 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 85 (accept_3_3 23 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 36 85 (Polychromatic418967fa.accept_16_6_4_5_1_2272 22 36 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 85 (Polychromatic418967fa.accept_10_1_6_5_1_304 21
  36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 85 (accept_3_3 20 36 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 85 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  19 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 85
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 85 (accept_3_3 17 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36
  85 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 36 85 (Polychromatic418967fa.accept_16_15_4_5_1_1411 15 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 85 (accept_3_3 14 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 36 85 (Polychromatic418967fa.accept_19_13_17_9_1_3312 13 36 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 85 (Polychromatic418967fa.accept_13_12_10_7_1_2433
  12 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 85 (accept_3_3 11 36
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 85
  (Polychromatic418967fa.accept_20_10_16_5_1_3311 10 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 36 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 85 (accept_3_3 8 36 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 36 85 (Polychromatic418967fa.accept_14_7_8_1_1_1621 7 36 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 85 (Polychromatic418967fa.accept_11_6_3_8_1_843 6
  36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 85 (accept_3_3 5 36 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 85 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 36
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 85
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 85 (accept_3_3 2 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 85
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 85)))))))))))))))))))))))))))))))))))) (allB_succ 35 85 (allA_of_3_1 35 35 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 85 (allA_succ_of_accept 33 34 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 85 (accept_3_3 32 34 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 34 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 85
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 34 85 (accept_3_3 29 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34
  85 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 34 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 85 (accept_3_3 26 34 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 34 85 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 34 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 85 (Polychromatic418967fa.accept_9_6_7_4_1_212 24
  34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 85 (accept_3_3 23 34 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 85 (Polychromatic418967fa.accept_13_9_8_7_1_1073
  22 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 85 (accept_3_3 20 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 34
  85 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 34 85 (Polychromatic418967fa.accept_19_18_15_9_1_3310 18 34 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 34 85 17 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 34 85 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 34 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 85 (accept_3_3 14 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 34
  85 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 85 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 34 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 85 (accept_3_3 11 34 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 85 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 34 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 85 (accept_3_3 8 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 85 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 34 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 85 (accept_3_3 5 34 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 85 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 34 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 85 (accept_3_3 2 34 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 85 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 34
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 85))))))))))))))))))))))))))))))))))
  (allB_succ 33 85 (allA_succ_of_accept 32 33 85 (accept_3_3 32 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 85 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 85 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 33 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 85 (accept_3_3 29 33 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 85
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 85 (accept_3_3 26 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33
  85 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 33 85 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 85 (accept_3_3 23 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 33 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 33 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 85 (Polychromatic418967fa.accept_9_3_6_4_1_210 21
  33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 85 (accept_3_3 20 33 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 85 (Polychromatic418967fa.accept_9_1_6_4_1_49 19
  33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 85
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 85 (accept_3_3 17 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33
  85 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 33 85 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 85 (accept_3_3 14 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 33 85 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 85 (Polychromatic418967fa.accept_8_4_1_5_1_186 12
  33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 85 (accept_3_3 11 33 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 85
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 85 (accept_3_3 8 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 85
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 85 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 85 (accept_3_3 5 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 85 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 85 (accept_3_3 2 33 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 85 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 33
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 85)))))))))))))))))))))))))))))))))
  (allB_succ 32 85 (allA_of_3_1 32 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 85 (allA_succ_of_accept
  30 31 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 31 85 (accept_3_3 29 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 31 85 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 31 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 85 (Polychromatic418967fa.accept_25_2_6_10_1_3309 27 31 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 85 (accept_3_3 26 31 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 85 (Polychromatic418967fa.accept_7_4_3_1_1_87 25
  31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 85
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 85 (accept_3_3 23 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31
  85 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 31 85 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 31 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 85 (accept_3_3 20 31 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 31 85 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 85 (accept_3_3 17 31 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 85 (Polychromatic418967fa.accept_7_2_3_1_1_10 16
  31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 85
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 85 (accept_3_3 14 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31
  85 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 85 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 85 (accept_3_3 11 31 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 85
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 85 (accept_3_3 8 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 85
  (Polychromatic418967fa.accept_15_7_1_10_1_305 7 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 85 (accept_3_3 5 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 31 85 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 31 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 85 (Polychromatic418967fa.accept_19_3_12_9_1_3308 3 31 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 85 (accept_3_3 2 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 85 (Polychromatic418967fa.accept_16_1_15_5_1_708 1 31 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 85))))))))))))))))))))))))))))))) (allB_succ
  30 85 (allA_succ_of_accept 29 30 85 (accept_3_3 29 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 30 85 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 85 (accept_3_3 26 30 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 85 5 5 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 30 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 30 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 85 (accept_3_3 23 30 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 85 (Polychromatic418967fa.accept_13_9_4_7_1_1694 22 30 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 30 85
  (Polychromatic418967fa.accept_18_3_12_13_1_3307 21 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 85 5 4 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 85 (Polychromatic418967fa.accept_20_18_10_5_1_3306 18 30 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 85 (accept_3_3 17 30 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 85 (Polychromatic418967fa.accept_9_7_3_4_1_218 16
  30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 85 5 3 6 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 85 (accept_3_3 14 30
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 85 (Polychromatic418967fa.accept_7_6_2_1_1_214
  13 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 85
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 85 (accept_3_3 11 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 85
  5 2 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 85
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 85 (accept_3_3 8 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 30 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 30 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 30 85 5 1 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 30 85 (Polychromatic418967fa.accept_20_4_10_5_1_3305 4 30 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 85 (accept_3_3 2 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 85
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 85)))))))))))))))))))))))))))))) (allB_succ 29 85 (allA_of_3_1 29 29 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 28 85 (allA_succ_of_accept 27 28 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 85 (accept_3_3 26 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 28 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 28 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 85
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 28 85 (accept_3_3 23 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28
  85 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 28 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 85 (accept_3_3 20 28 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 28 85 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 28 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 85 (Polychromatic418967fa.accept_13_5_2_7_1_2414
  18 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 85 (accept_3_3 17 28
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 85 (Polychromatic418967fa.accept_9_7_1_4_1_217
  16 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 85 (accept_3_3 14 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 28
  85 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 28 85 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 28 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 85 (accept_3_3 11 28 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 28 85 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 85 (accept_3_3 8 28 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 85 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 85
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 85 (accept_3_3 5 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 85
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 85 (accept_3_3 2 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 28 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 28 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 85)))))))))))))))))))))))))))) (allB_succ 27 85 (allA_succ_of_accept 26
  27 85 (accept_3_3 26 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 85
  (Polychromatic418967fa.accept_11_3_5_8_1_458 25 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 85 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 27 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 85 (accept_3_3 23 27 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 27 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 85 (Polychromatic418967fa.accept_12_9_3_1_1_303 21
  27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 85 (accept_3_3 20 27 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 85 (Polychromatic418967fa.accept_7_5_6_1_1_407 19
  27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 85
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 85 (accept_3_3 17 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27
  85 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 27 85 (Polychromatic418967fa.accept_20_15_7_5_1_2115 15 27 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 85 (accept_3_3 14 27 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 27 85 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 85 (Polychromatic418967fa.accept_7_5_6_1_1_407 12
  27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 85 (accept_3_3 11 27 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 85
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 85 (accept_3_3 8 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 85
  (Polychromatic418967fa.accept_14_7_13_1_1_922 7 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 85 (accept_3_3 5 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 85 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 27 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 85 (accept_3_3 2 27 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 85 (Polychromatic418967fa.accept_19_1_8_9_1_3304 1 27 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 85))))))))))))))))))))))))))) (allB_succ 26
  85 (allA_of_3_1 26 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 85 (allA_succ_of_accept 24 25 85
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 85 (accept_3_3 23 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25
  85 (Polychromatic418967fa.accept_18_4_7_13_1_3303 22 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 85 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 25 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 85 5 4 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 85 (Polychromatic418967fa.accept_7_5_4_1_1_412 19
  25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 85
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 85 (accept_3_3 17 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25
  85 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 25 85 5 3 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 25 85 (accept_3_3 14 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25
  85 (Polychromatic418967fa.accept_16_13_9_5_1_3302 13 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 85 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 85 (accept_3_3 11 25 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 85 5 2 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 25 85 (Polychromatic418967fa.accept_23_9_2_16_1_3301 9 25 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 85 (accept_3_3 8 25 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 85 (Polychromatic418967fa.accept_21_7_4_1_1_3300 7 25 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 85
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 85 5 1 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 85 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 25 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 85 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 25 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 85 (accept_3_3 2 25 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 85 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 25 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 85))))))))))))))))))))))))) (allB_succ 24 85
  (allA_succ_of_accept 23 24 85 (accept_3_3 23 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24
  85 (Polychromatic418967fa.accept_13_9_11_7_1_1077 22 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 24 85 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 85 (accept_3_3 20 24 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 85 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 24 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 85
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 85 (accept_3_3 17 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24
  85 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 24 85 (Polychromatic418967fa.accept_19_15_5_9_1_3299 15 24 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 85 (accept_3_3 14 24 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 24 85 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 24 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 85 (Polychromatic418967fa.accept_7_5_3_1_1_424 12
  24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 85 (accept_3_3 11 24 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 85 (Polychromatic418967fa.accept_9_1_6_4_1_49 10
  24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 85
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 85 (accept_3_3 8 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 85
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 24 85 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 24 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 85 (accept_3_3 5 24 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 24 85 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 24 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 85 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 85 (accept_3_3 2 24 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 85 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 24
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 85)))))))))))))))))))))))) (allB_succ 23
  85 (allA_of_3_1 23 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 85 (allA_succ_of_accept 21 22 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 85 (accept_3_3 20 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22
  85 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 22 85 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 22 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 85 (accept_3_3 17 22 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 22 85 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 22 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 85 (accept_3_3 14 22 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 85 (Polychromatic418967fa.accept_10_3_2_5_1_295 13
  22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 85
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 22 85 (accept_3_3 11 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22
  85 (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 22 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 85 (accept_3_3 8 22 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 22 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 85 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6
  22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 85 (accept_3_3 5 22 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 85 (Polychromatic418967fa.accept_12_4_10_1_1_706 4
  22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 85 (accept_3_3 2 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 85
  (Polychromatic418967fa.accept_15_1_7_10_1_287 1 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 85)))))))))))))))))))))) (allB_succ 21 85 (allA_succ_of_accept 20 21 85 (accept_3_3 20 21 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 85 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 21 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 85
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 85 (accept_3_3 17 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21
  85 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 21 85 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 85 (accept_3_3 14 21 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 21 85 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 21 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 85 (Polychromatic418967fa.accept_13_12_8_7_1_2526
  12 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 85 (accept_3_3 11 21
  85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 85 (Polychromatic418967fa.accept_6_4_3_1_1_57
  10 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 85
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 85 (accept_3_3 8 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 85
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 85 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 85 (accept_3_3 5 21 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 85 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 85 (accept_3_3 2 21 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 85 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 21
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 85))))))))))))))))))))) (allB_succ 20 85
  (allA_of_3_1 20 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 85 (allA_succ_of_accept 18 19 85
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 85 (accept_3_3 17 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19
  85 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 19 85 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 19 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 85 (accept_3_3 14 19 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 19 85 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 19 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 85 (Polychromatic418967fa.accept_9_3_1_4_1_216 12
  19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 85 (accept_3_3 11 19 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 85
  (Polychromatic418967fa.accept_13_9_6_7_1_551 9 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 85 (accept_3_3 8 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 85
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 85 (accept_3_3 5 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 19 85 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 19 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 85 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 85 (accept_3_3 2 19 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 85 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 19 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 85))))))))))))))))))) (allB_succ 18 85
  (allA_succ_of_accept 17 18 85 (accept_3_3 17 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18
  85 (Polychromatic418967fa.accept_19_16_18_9_1_3295 16 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 85 (accept_3_3 14 18 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 85 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 18 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 85
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 85 (accept_3_3 11 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18
  85 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 18 85 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 18 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 85 (accept_3_3 8 18 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 18 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 85 (Polychromatic418967fa.accept_15_6_3_10_1_2341 6
  18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 85 (accept_3_3 5 18 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 85 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4
  18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 85 (accept_3_3 2 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 85
  (Polychromatic418967fa.accept_22_1_18_19_1_3294 1 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 85)))))))))))))))))) (allB_succ 17 85 (allA_of_3_1 17 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 85 (allA_succ_of_accept 15 16 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 85 (accept_3_3 14 16 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 16 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 85
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 85 (accept_3_3 11 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16
  85 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 16 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 85 (accept_3_3 8 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 16 85 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 16 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 16 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 85 (accept_3_3 5 16 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 85 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 16 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 85
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 85 (accept_3_3 2 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 85
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 85)))))))))))))))) (allB_succ 15 85 (allA_succ_of_accept 14 15 85 (accept_3_3 14 15 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 85 (Polychromatic418967fa.accept_19_13_15_9_1_3293 13 15 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 85
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 15 85 (accept_3_3 11 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 85
  5 2 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 85
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 85 (accept_3_3 8 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 85
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 85 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 5 15 85 5 1 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 4 15 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 85
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 85 (accept_3_3 2 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 85
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 85))))))))))))))) (allB_succ 14 85 (allA_of_3_1 14 14 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 13 85 (allA_succ_of_accept 12 13 85 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 85 (accept_3_3 11 13 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 85 (Polychromatic418967fa.accept_16_10_13_5_1_3292 10 13 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 85
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 13 85 (accept_3_3 8 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 85
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 13 85 (Polychromatic418967fa.accept_19_6_13_9_1_3291 6 13 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 85 (accept_3_3 5 13 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 13 85 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 13 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 85 (Polychromatic418967fa.accept_15_3_13_10_1_2332
  3 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 85 (accept_3_3 2 13 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 85 (Polychromatic418967fa.accept_15_1_13_10_1_1507
  1 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 85))))))))))))) (allB_succ 12 85
  (allA_succ_of_accept 11 12 85 (accept_3_3 11 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12
  85 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 12 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 85 (accept_3_3 8 12 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 85 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 85 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 12
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 85 (accept_3_3 5 12 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 85 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 12
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 85
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 85 (accept_3_3 2 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 85
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 85)))))))))))) (allB_succ 11 85 (allA_of_3_1 11 11 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  10 85 (allA_succ_of_accept 9 10 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 85 (accept_3_3 8 10 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 10 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 85 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 10
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 10 85 5 1 2 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 10 85
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 85 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 85 (accept_3_3 2 10 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 85 (Polychromatic418967fa.accept_18_1_10_13_1_500 1 10 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 85)))))))))) (allB_succ 9 85 (allA_succ_of_accept 8 9 85
  (accept_3_3 8 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 85
  (Polychromatic418967fa.accept_20_7_9_5_1_292 7 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 85 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 85 (accept_3_3 5 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 85 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 85 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 85 (accept_3_3 2 9 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 85 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 9 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 85))))))))) (allB_succ 8 85 (allA_of_3_1 8 8 85
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 85 (allA_succ_of_accept 6 7 85
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 85 (accept_3_3 5 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 85
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 85 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 85 (accept_3_3 2 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 7 85 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 7 85))))))) (allB_succ 6 85 (allA_succ_of_accept 5 6 85 (accept_3_3 5 6 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 85 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 6 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 85
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 85 (accept_3_3 2 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 85
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 85)))))) (allB_succ 5 85 (allA_of_3_1 5 5 85 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 4 85
  (allA_succ_of_accept 3 4 85 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 4 85 (accept_3_3 2 4 85 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 4 85 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 4 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 4 85)))) (allB_succ 3 85 (allA_succ_of_accept 2 3 85 (accept_3_3 2 3 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 85 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 3 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 85))) (allB_succ 2 85 (allA_of_3_1 2 2 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_two
  85)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


