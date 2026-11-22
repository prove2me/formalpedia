-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch88
-- name    : Polychromatic418967fa_Branch88
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:21.007241+00:00
-- url     : https://prove2.me/theorems/11194a62-fe36-405d-9cf4-2703ce5e38b4
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

def Polychromatic418967fa.branch_88 : allB 88 88 :=
  allB_succ' 2 87 88 (Eq.refl Bool.true) (allA_succ_of_accept 1 87 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 88)) (allB_succ' 3 86 88 (Eq.refl Bool.true)
  (allA_of_3_1 3 86 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 85 88 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 85 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 88 (accept_3_3 2 85 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 88)))) (allB_succ' 5 84 88 (Eq.refl Bool.true) (allA_succ_of_gcd
  4 84 88 4 1 21 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 84 88 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 84 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 84 88 2 1 42 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 84 88 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 88))))) (allB_succ' 6 83 88 (Eq.refl Bool.true) (allA_of_3_1 6 83 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 82 88 (Eq.refl Bool.true) (allA_succ_of_gcd 6 82 88 2 3 41 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 88
  (accept_3_3 5 82 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 88 2 2 41 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82 88
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 82 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 82 88 2 1 41 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 82 88 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 82 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 82 88))))))) (allB_succ' 8 81 88 (Eq.refl Bool.true) (allA_succ_of_accept 7
  81 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 88 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 81 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 88 (accept_3_3 5 81 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 88 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 81 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 88 (Polychromatic418967fa.accept_10_3_1_8_1_132 3
  81 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 88 (accept_3_3 2 81 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 88)))))))) (allB_succ' 9 80 88 (Eq.refl
  Bool.true) (allA_of_3_1 9 80 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 79 88 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 79 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 88 (accept_3_3 8 79 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 79 88 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 79 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 88 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 88 (accept_3_3 5 79 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 88 (Polychromatic418967fa.accept_10_4_9_8_1_125 4
  79 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 88 (accept_3_3 2 79 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 88
  (Polychromatic418967fa.accept_10_1_9_8_1_123 1 79 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 88)))))))))) (allB_succ' 11 78 88 (Eq.refl Bool.true) (allA_succ_of_gcd 10 78 88 2 5 39 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 88
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 78 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 88 2 4 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 88 (Polychromatic418967fa.accept_17_7_10_3_1_1421 7 78 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 88 2 3 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 88 (accept_3_3 5 78 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 88 2 2 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 88 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 88 2 1 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 88 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 88))))))))))) (allB_succ' 12 77 88
  (Eq.refl Bool.true) (allA_of_3_1 12 77 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 76 88 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 76 88 4 3 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 76 88 (accept_3_3 11 76 88 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 76 88 2 5 38 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 76 88 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 76 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 88 4 2 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 88 (Polychromatic418967fa.accept_16_7_12_8_1_2450 7 76 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 88 2 3 38 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 88 (accept_3_3 5 76 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 88 4 1 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 88 2 1 38 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 88
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 88))))))))))))) (allB_succ' 14 75 88 (Eq.refl Bool.true) (allA_succ_of_accept 13 75 88
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 88 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 75 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 88 (accept_3_3 11 75 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 75 88 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 75 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 88 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 88 (accept_3_3 8 75 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 88
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 88 (accept_3_3 5 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 88
  (Polychromatic418967fa.accept_9_4_3_7_1_296 4 75 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 88 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 75 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 88 (accept_3_3 2 75 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 88)))))))))))))) (allB_succ' 15 74 88 (Eq.refl Bool.true)
  (allA_of_3_1 15 74 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 73 88 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 73 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 88 (accept_3_3 14 73 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 73 88 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 88 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 88 (accept_3_3 11 73 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 88 (Polychromatic418967fa.accept_12_10_1_4_1_392
  10 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 88 (accept_3_3 8 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 88
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 73 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 88 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 73 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 88 (accept_3_3 5 73 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 88 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 88 (accept_3_3 2 73 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 88 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 88)))))))))))))))) (allB_succ' 17 72 88
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 72 88 8 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 72 88 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 72 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 88 2 7 36 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 88
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 88 4 3 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 88 (accept_3_3 11 72 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 88
  2 5 36 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 88
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 72 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 88 8 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 88 (Polychromatic418967fa.accept_17_7_4_3_1_3456 7 72 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 88 2 3 36 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 88 (accept_3_3 5 72 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 88 4 1 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 88 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 72 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 88 2 1 36 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 88 (Polychromatic418967fa.accept_15_1_12_13_1_944 1
  72 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 88))))))))))))))))) (allB_succ' 18 71
  88 (Eq.refl Bool.true) (allA_of_3_1 18 71 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 70 88 (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 70 88 2 9 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 70 88 (accept_3_3 17 70 88 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 70 88 2 8 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 70 88 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 70 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 88 2 7 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 88 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 70 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 88 2 6 35 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 88 (accept_3_3 11 70 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 88 2 5 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 88 (Polychromatic418967fa.accept_24_9_22_16_1_826 9
  70 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 88 2 4 35 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 88
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 70 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 70 88 2 3 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 70 88 (accept_3_3 5 70 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 88 2
  2 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 88
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 3 70 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 70 88 2 1 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 70 88 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 70 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 70 88))))))))))))))))))) (allB_succ' 20 69 88 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 69 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 88 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 69 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 88 (accept_3_3 17 69 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 88 (Polychromatic418967fa.accept_7_2_6_4_1_29 16
  69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 88
  (Polychromatic418967fa.accept_17_15_1_3_1_1488 15 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 88 (accept_3_3 14 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69
  88 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 69 88 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 88 (accept_3_3 11 69 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 69 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 69 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 88 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 88 (accept_3_3 8 69 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 88
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 88 (accept_3_3 5 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 88
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 69 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 88 (accept_3_3 2 69 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 88)))))))))))))))))))) (allB_succ' 21 68 88 (Eq.refl Bool.true)
  (allA_of_3_1 21 68 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 67 88 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 67 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 88 (accept_3_3 20 67 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 67 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 88 (Polychromatic418967fa.accept_13_5_2_10_1_248
  18 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 88 (accept_3_3 17 67
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 88
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 16 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 67 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 88 (accept_3_3 14 67 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 67 88 (Polychromatic418967fa.accept_16_13_3_8_1_2422 13 67 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 88 (Polychromatic418967fa.accept_9_3_4_7_1_89 12
  67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 88 (accept_3_3 11 67 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 67
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 88 (accept_3_3 8 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 88
  (Polychromatic418967fa.accept_14_7_11_4_1_3455 7 67 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 88 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 67 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 88 (accept_3_3 5 67 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 88 (Polychromatic418967fa.accept_16_4_3_8_1_2486 4 67 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 88 (accept_3_3 2 67 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 67
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 88)))))))))))))))))))))) (allB_succ' 23
  66 88 (Eq.refl Bool.true) (allA_succ_of_gcd 22 66 88 22 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 88 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 66 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 88 2 10 33 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 88
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 88 2 9 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 88 (accept_3_3 17 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 88
  2 8 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66
  88 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 66 88 2 7 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 88 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 66 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 88 2 6 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 66 88 11 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 66 88 2 5 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 88 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 66 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 88 2 4 33 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 88
  (Polychromatic418967fa.accept_14_7_10_4_1_130 7 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 88 2 3 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 88 (accept_3_3 5 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 88 2
  2 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 88
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 66 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 66 88 2 1 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 88 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 66 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 88))))))))))))))))))))))) (allB_succ' 24 65 88 (Eq.refl Bool.true)
  (allA_of_3_1 24 65 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 64 88 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 64 88 8 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 88 (accept_3_3 23 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 88
  2 11 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64
  88 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 64 88 4 5 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 64 88 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 64 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 88 2 9 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 88 (accept_3_3 17 64 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 64 88 8 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 64 88 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 64 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 88 2 7 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 88 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  64 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 88 4 3 16 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 88 (accept_3_3 11 64
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 88 2 5 32 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 88
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 64 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 88 8 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 88 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 64 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 88 2 3 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 88 (accept_3_3 5 64 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 88 4 1 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 88 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 64 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 88 2 1 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 88 (Polychromatic418967fa.accept_18_1_10_16_1_566 1
  64 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 88)))))))))))))))))))))))))
  (allB_succ' 26 63 88 (Eq.refl Bool.true) (allA_succ_of_accept 25 63 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 88
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 88 (accept_3_3 23 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63
  88 (Polychromatic418967fa.accept_29_22_5_1_1_3454 22 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 63 88 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 63 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 88 (accept_3_3 20 63 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 88
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 88 (accept_3_3 17 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63
  88 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 63 88 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 63 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 88 (accept_3_3 14 63 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 63 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 88
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 88 (accept_3_3 11 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63
  88 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 88 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 63 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 88 (accept_3_3 8 63 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 63 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 88 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6
  63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 88 (accept_3_3 5 63 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 88 (Polychromatic418967fa.accept_13_4_11_10_1_1226
  4 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 88
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 88 (accept_3_3 2 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 88
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 88)))))))))))))))))))))))))) (allB_succ' 27 62 88 (Eq.refl Bool.true) (allA_of_3_1 27 62 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 61 88 (Eq.refl Bool.true) (allA_succ_of_accept 27 61 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 61 88 (accept_3_3 26 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61
  88 (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 61 88 (Polychromatic418967fa.accept_17_7_10_3_1_1421 24 61 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 88 (accept_3_3 23 61 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 88 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 61 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 61 88 (accept_3_3 20 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61
  88 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 61 88 (Polychromatic418967fa.accept_15_3_1_13_1_1672 18 61 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 88 (accept_3_3 17 61 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 61 88 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 61 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 15
  61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 88 (accept_3_3 14 61 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 88 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 88
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 88 (accept_3_3 11 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61
  88 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 61 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 88 (accept_3_3 8 61 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 61 88 (Polychromatic418967fa.accept_17_7_10_3_1_1421 7 61 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 88 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 61
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 88 (accept_3_3 5 61 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 88 (Polychromatic418967fa.accept_16_4_13_8_1_3424 4
  61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 88 (accept_3_3 2 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 88
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 61 88)))))))))))))))))))))))))))) (allB_succ' 29 60 88 (Eq.refl Bool.true) (allA_succ_of_gcd 28 60 88 4 7 15
  22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 88
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 60 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 60 88 2 13 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 60 88 (Polychromatic418967fa.accept_13_12_8_10_1_1879 25 60 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 88 4 6 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 88 (accept_3_3 23 60 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 60 88 2 11 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 60 88 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 88 4 5 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 88 (Polychromatic418967fa.accept_9_1_6_7_1_285 19
  60 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 88 2 9 30 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 88 (accept_3_3 17 60
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 88 4 4 15 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 88
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 60 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 60 88 2 7 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 88 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 60 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 88 4 3 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 88 (accept_3_3 11 60 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 88 2 5 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 60 88 (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 60 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 88 4 2 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 88 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7
  60 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 88 2 3 30 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 88 (accept_3_3 5 60
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 88 4 1 15 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 88
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 88 2 1 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 88 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 88))))))))))))))))))))))))))))) (allB_succ' 30 59 88 (Eq.refl Bool.true)
  (allA_of_3_1 30 59 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 58 88 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 58 88 2 15 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 88 (accept_3_3 29 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 88
  2 14 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58
  88 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 58 88 2 13 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 58 88 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 58 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 88 2 12 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 88 (accept_3_3 23 58 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 58 88 2 11 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 88 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 58 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 88 2 10 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 88 (Polychromatic418967fa.accept_7_5_2_4_1_126 19
  58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 88 2 9 29 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 88 (accept_3_3 17 58
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58 88 2 8 29 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 58 88
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 58 88 2 7 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 58 88 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 58 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 88 2 6 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 88 (accept_3_3 11 58 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 58 88 2 5 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 58 88 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 58 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 58 88 2 4 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 58 88 (Polychromatic418967fa.accept_12_7_10_4_1_382 7
  58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 88 2 3 29 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 88 (accept_3_3 5 58
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 88 2 2 29 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 58 88
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 58 88 2 1 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 58 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 58 88 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 58 88))))))))))))))))))))))))))))))) (allB_succ' 32 57 88 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 57 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 88 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 57 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 88 (accept_3_3 29 57 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 88 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 57
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 88
  (Polychromatic418967fa.accept_20_7_17_8_1_3452 27 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 88 (accept_3_3 26 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57
  88 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 88 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 88 (accept_3_3 23 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 88 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 57 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 88 (Polychromatic418967fa.accept_13_8_5_10_1_2701
  21 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 88 (accept_3_3 20 57
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 88
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 88 (accept_3_3 17 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57
  88 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 88 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 57 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 88 (accept_3_3 14 57 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 88
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 88 (accept_3_3 11 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57
  88 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 57 88 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 88 (accept_3_3 8 57 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 57 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 88 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 88 (accept_3_3 5 57 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 88 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 57
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 88
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 88 (accept_3_3 2 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 88
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 88)))))))))))))))))))))))))))))))) (allB_succ' 33 56 88 (Eq.refl Bool.true) (allA_of_3_1 33 56 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 55 88 (Eq.refl Bool.true) (allA_succ_of_gcd 33 55 88 11 3 5 8
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 55 88
  (accept_3_3 32 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 88
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 55 88 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 88 (accept_3_3 29 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 55 88 (Polychromatic418967fa.accept_13_2_3_10_1_658 28 55 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 88 (accept_3_3 26 55 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 88 (Polychromatic418967fa.accept_16_9_7_8_1_1588
  25 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 88
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 88 (accept_3_3 23 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 55 88
  11 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 55 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 88 (accept_3_3 20 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55
  88 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 88 (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 88 (accept_3_3 17 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 88 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 55 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 15
  55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 88 (accept_3_3 14 55 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 88 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 88
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 55 88 11 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 55 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 88 (accept_3_3 8 55 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 88 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 55 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 88
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 88 (accept_3_3 5 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 88
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 55 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 88 (accept_3_3 2 55 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 88 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 55 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 88)))))))))))))))))))))))))))))))))) (allB_succ' 35 54 88
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 54 88 2 17 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 54 88 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 88 2 16 27 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 88
  (Polychromatic418967fa.accept_13_5_2_10_1_248 31 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 88 2 15 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 88 (accept_3_3 29 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 88
  2 14 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54
  88 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 88 2 13 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 88 (Polychromatic418967fa.accept_13_12_2_10_1_2698 25 54 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 88 2 12 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 88 (accept_3_3 23 54 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 88 2 11 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 54 88 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 88 2 10 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 88 (Polychromatic418967fa.accept_10_9_4_8_1_741 19
  54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 88 2 9 27 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 88 (accept_3_3 17 54
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 88 2 8 27 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 88
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 88 2 7 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 88 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 54 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 88 2 6 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 88 (accept_3_3 11 54 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 88 2 5 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 88 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 54 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 88 2 4 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 88 (Polychromatic418967fa.accept_15_7_9_13_1_3451 7
  54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 88 2 3 27 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 88 (accept_3_3 5 54
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 88 2 2 27 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 88
  (Polychromatic418967fa.accept_12_3_6_4_1_400 3 54 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 88 2 1 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 88 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 54 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 88))))))))))))))))))))))))))))))))))) (allB_succ' 36 53 88 (Eq.refl
  Bool.true) (allA_of_3_1 36 53 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 52 88 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 52 88 4 9 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 88 (accept_3_3 35 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 88
  2 17 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52
  88 (Polychromatic418967fa.accept_16_1_4_8_1_3434 33 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 52 88 4 8 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 52 88 (Polychromatic418967fa.accept_16_15_4_8_1_1562 31 52 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 88 2 15 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 88 (accept_3_3 29 52 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 52 88 4 7 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 52 88 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 88 2 13 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 88 (Polychromatic418967fa.accept_10_5_2_8_1_135 25
  52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 88 4 6 13 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 88 (accept_3_3 23 52
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 88 2 11 26 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 88
  (Polychromatic418967fa.accept_14_7_10_4_1_130 21 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 52 88 4 5 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 52 88 (Polychromatic418967fa.accept_16_3_4_8_1_3450 19 52 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 88 2 9 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 88 (accept_3_3 17 52 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 52 88 4 4 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 52 88 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 52 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 88 2 7 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 88 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 88 4 3 13 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 88 (accept_3_3 11 52
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 88 2 5 26 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 88
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 52 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 88 4 2 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 88 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 52 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 88 2 3 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 88 (accept_3_3 5 52 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 88 4 1 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 88 (Polychromatic418967fa.accept_16_3_4_8_1_3450 3 52 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 88 2 1 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 88 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 52
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 88)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 51 88 (Eq.refl Bool.true) (allA_succ_of_accept 37 51 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 51
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 88
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 36 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 88 (accept_3_3 35 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51
  88 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 51 88 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 88 (accept_3_3 32 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 51 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 88 (Polychromatic418967fa.accept_9_3_6_7_1_562 30
  51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 88 (accept_3_3 29 51 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 88 (Polychromatic418967fa.accept_9_1_6_7_1_285 28
  51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 88
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 88 (accept_3_3 26 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51
  88 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 51 88 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 88 (accept_3_3 23 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 51 88 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 51 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 88 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 88 (accept_3_3 20 51 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 88
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 88 (accept_3_3 17 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51
  88 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 51 88 (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 88 (accept_3_3 14 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 51 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 88 (Polychromatic418967fa.accept_7_5_2_4_1_126 12
  51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 88 (accept_3_3 11 51 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 88 (Polychromatic418967fa.accept_9_1_6_7_1_285 10
  51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 88
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 88 (accept_3_3 8 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 88
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 88 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 88 (accept_3_3 5 51 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 88 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 51 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 88 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 51
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 88 (accept_3_3 2 51 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 88))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 50 88 (Eq.refl Bool.true) (allA_of_3_1 39 50 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40
  49 88 (Eq.refl Bool.true) (allA_succ_of_accept 39 49 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 88 (accept_3_3 38 49 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 88
  (Polychromatic418967fa.accept_15_6_4_13_1_403 36 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 88 (accept_3_3 35 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49
  88 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 49 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 88 (accept_3_3 32 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 49 88 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 49 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 88 (Polychromatic418967fa.accept_9_3_4_7_1_89 30
  49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 88 (accept_3_3 29 49 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 88 (accept_3_3 26 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49
  88 (Polychromatic418967fa.accept_14_11_7_4_1_3449 25 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 88 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 88 (accept_3_3 23 49 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 88 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 88 (accept_3_3 20 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49
  88 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 88 (Polychromatic418967fa.accept_17_1_15_3_1_1501 18 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 88 (accept_3_3 17 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 88 (Polychromatic418967fa.accept_21_16_7_4_1_3448 16 49 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 15
  49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 88 (accept_3_3 14 49 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 88
  (Polychromatic418967fa.accept_19_13_11_12_1_3447 13 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 49 88 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 88 (accept_3_3 11 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 49 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 88 (accept_3_3 8 49 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 88 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7
  49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 88
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 88 (accept_3_3 5 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 88
  (Polychromatic418967fa.accept_10_4_9_8_1_125 4 49 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 88 (accept_3_3 2 49 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 88)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 48 88
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 48 88 8 5 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 88 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 48 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 88 2 19 24 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 88
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 88 4 9 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 88 (accept_3_3 35 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 88
  2 17 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48
  88 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 88 8 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 88 2 15 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 88 (accept_3_3 29 48 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 88 4 7 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 88 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 48 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 88 2 13 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 88 (Polychromatic418967fa.accept_13_12_9_10_1_1223
  25 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 88 8 3 6 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 88 (accept_3_3 23 48
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 88 2 11 24 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 88
  (Polychromatic418967fa.accept_19_2_10_12_1_3446 21 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 88 4 5 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 88 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 88 2 9 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 88 (accept_3_3 17 48 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 88 8 2 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 88 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 88 2 7 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 88 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 88 4 3 12 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 88 (accept_3_3 11 48
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 88 2 5 24 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 88
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 88 8 1 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 88 (Polychromatic418967fa.accept_21_7_6_4_1_3445 7 48 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 88 2 3 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 88 (accept_3_3 5 48 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 88 4 1 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 88 2 1 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 88 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 88)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 47 88 (Eq.refl Bool.true) (allA_of_3_1 42 47 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43
  46 88 (Eq.refl Bool.true) (allA_succ_of_gcd 42 46 88 2 21 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 88 (accept_3_3 41 46 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 46 88 2 20 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 46 88 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 46 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 88 2 19 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 88 (Polychromatic418967fa.accept_12_1_10_4_1_380 37
  46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 88 2 18 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 88 (accept_3_3 35 46
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 88 2 17 23 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 88
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 46 88 2 16 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 46 88 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 46 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 88 2 15 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 88 (accept_3_3 29 46 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 46 88 2 14 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 88 (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 46 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 88 2 13 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 88 (Polychromatic418967fa.accept_12_1_10_4_1_380 25
  46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 88 2 12 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 88 (accept_3_3 23 46
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 88 2 11 23 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 88
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 88 2 10 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 88 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 46 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 88 2 9 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 88 (accept_3_3 17 46 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 88 2 8 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 88 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 46 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 88 2 7 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 88 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 88 2 6 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 88 (accept_3_3 11 46
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 88 2 5 23 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 88
  (Polychromatic418967fa.accept_24_9_22_16_1_826 9 46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 88 2 4 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 88 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 46 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 88 2 3 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 88 (accept_3_3 5 46 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 88 2 2 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 88 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 46 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 88 2 1 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 88 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  46 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  88))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 45 88 (Eq.refl Bool.true) (allA_succ_of_accept 43 45 88
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 88 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 88 (accept_3_3 41 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 88 (Polychromatic418967fa.accept_25_15_20_13_1_753 40 45 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 88 (Polychromatic418967fa.accept_19_1_7_12_1_3443
  39 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 88 (accept_3_3 38 45
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 37
  45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 88
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 88 (accept_3_3 35 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45
  88 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 45 88 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 88 (accept_3_3 32 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 45 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 45 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 88 (Polychromatic418967fa.accept_12_6_9_4_1_96 30
  45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 88 (accept_3_3 29 45 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 88 (Polychromatic418967fa.accept_13_2_6_10_1_2703
  28 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 88
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 88 (accept_3_3 26 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45
  88 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 45 88 (Polychromatic418967fa.accept_19_5_7_12_1_2252 24 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 88 (accept_3_3 23 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 45 88 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 45 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 88 (Polychromatic418967fa.accept_14_7_3_4_1_1816
  21 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 88 (accept_3_3 20 45
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 88
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 88 (accept_3_3 17 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45
  88 (Polychromatic418967fa.accept_13_3_6_10_1_2658 16 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 88 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 45 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 88 (accept_3_3 14 45 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 88
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 88 (accept_3_3 11 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45
  88 (Polychromatic418967fa.accept_17_10_11_3_1_3442 10 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 88 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 45 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 88 (accept_3_3 8 45 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 45 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 88 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 88 (accept_3_3 5 45 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 88 (Polychromatic418967fa.accept_13_4_6_10_1_1199 4
  45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 88
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 88 (accept_3_3 2 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 88
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 88)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 88 (allA_of_3_1 44 44 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 43 88 (allA_succ_of_accept 42 43 88 (Polychromatic418967fa.accept_19_4_5_12_1_3441 42
  43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 88 (accept_3_3 41 43 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 88 (Polychromatic418967fa.accept_7_5_1_4_1_122 40
  43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 88 (accept_3_3 38 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43
  88 (Polychromatic418967fa.accept_13_11_4_10_1_3440 37 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 88 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 43 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 88 (accept_3_3 35 43 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 88 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 43 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 88 (accept_3_3 32 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43
  88 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 43 88 (Polychromatic418967fa.accept_19_11_5_12_1_3439 30 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 88 (accept_3_3 29 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 43 88 (Polychromatic418967fa.accept_16_12_11_8_1_832 28 43 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 88 (accept_3_3 26 43 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 88 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  25 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 88
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 88 (accept_3_3 23 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43
  88 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 43 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 88 (accept_3_3 20 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 43 88 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 88 (Polychromatic418967fa.accept_13_5_4_10_1_1244
  18 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 88 (accept_3_3 17 43
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 88
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 43 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 88 (accept_3_3 14 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 43 88 (Polychromatic418967fa.accept_16_13_11_8_1_2449 13 43 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 88 (Polychromatic418967fa.accept_7_5_1_4_1_122 12
  43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 88 (accept_3_3 11 43 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 88 (Polychromatic418967fa.accept_7_3_1_4_1_121 10
  43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 88 (accept_3_3 8 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 88
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 88 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 88 (accept_3_3 5 43 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 88 (Polychromatic418967fa.accept_16_4_11_8_1_1574 4 43 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 88 (accept_3_3 2 43 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 88 (Polychromatic418967fa.accept_10_1_3_8_1_136 1
  43 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  88))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 88 (allA_succ_of_accept 41 42 88 (accept_3_3 41 42 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 88 2 20 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 88 (Polychromatic418967fa.accept_9_3_6_7_1_562 39
  42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 88 2 19 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 88
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 88 2 18 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 88 (accept_3_3 35 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 88
  2 17 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42
  88 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 88 2 16 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 88 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 88 2 15 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 88 (accept_3_3 29 42 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 42 88 2 14 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 42 88 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 42 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 88 2 13 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 88 (Polychromatic418967fa.accept_10_5_2_8_1_135 25
  42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 88 2 12 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 88 (accept_3_3 23 42
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 88 2 11 21 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 88
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 88 2 10 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 88 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 88 2 9 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 88 (accept_3_3 17 42 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 88 2 8 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 88 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 42 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 88 2 7 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 88 (Polychromatic418967fa.accept_9_4_6_7_1_286 13
  42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 88 2 6 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 88 (accept_3_3 11 42
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 88 2 5 21 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 88
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 88 2 4 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 88 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 42 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 88 2 3 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 88 (accept_3_3 5 42 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 88 2 2 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 88 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 88 2 1 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 88 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  88)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 88 (allA_of_3_1 41 41 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 88 (allA_succ_of_accept 39 40 88 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 40 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 88 2 19 20 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 88
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 88 4 9 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 40 88 (accept_3_3 35 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 88
  2 17 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40
  88 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 40 88 8 4 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 40 88 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 40 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 88 2 15 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 88 (accept_3_3 29 40 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 40 88 4 7 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 40 88 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 88 2 13 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 88 (Polychromatic418967fa.accept_18_7_4_16_1_2299
  25 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 88 8 3 5 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 88 (accept_3_3 23 40
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 88 2 11 20 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 88
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 88 4 5 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 88 2 9 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 88 (accept_3_3 17 40 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 88 8 2 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 88 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 40 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 88 2 7 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 88 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 88 4 3 10 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 88 (accept_3_3 11 40
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 88 2 5 20 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 88
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 88 8 1 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 88 (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 40 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 88 2 3 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 88 (accept_3_3 5 40 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 88 4 1 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 88 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 40 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 88 2 1 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 88 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 40
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  88)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 88 (allA_succ_of_accept 38 39 88 (accept_3_3 38 39 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 88
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 88 (accept_3_3 35 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39
  88 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 39 88 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 39 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 88 (accept_3_3 32 39 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 39 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 88 (Polychromatic418967fa.accept_12_6_3_4_1_394 30
  39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 88 (accept_3_3 29 39 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 88 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 39
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 88
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 88 (accept_3_3 26 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39
  88 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 88 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 88 (accept_3_3 23 39 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 88 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 39 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 88 (Polychromatic418967fa.accept_10_1_9_8_1_123 21
  39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 88 (accept_3_3 20 39 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 88
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 88 (accept_3_3 17 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39
  88 (Polychromatic418967fa.accept_26_16_13_10_1_3437 16 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 88 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 39 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 88 (accept_3_3 14 39 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 88
  (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 88 (accept_3_3 11 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39
  88 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 39 88 (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 39 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 88 (accept_3_3 8 39 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 39 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 88 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 39
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 88 (accept_3_3 5 39 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 88 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 39
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 88
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 39 88 (accept_3_3 2 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 88
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 39 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 39 88))))))))))))))))))))))))))))))))))))))) (allB_succ 38 88 (allA_of_3_1 38 38 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 37 88 (allA_succ_of_accept 36 37 88 (Polychromatic418967fa.accept_15_6_7_13_1_1666 36
  37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 88 (accept_3_3 35 37 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 88 (Polychromatic418967fa.accept_7_6_2_4_1_291 34
  37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 88 (accept_3_3 32 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37
  88 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 88 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 88 (accept_3_3 29 37 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 88 (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 37 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 88 (accept_3_3 26 37 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 88 (Polychromatic418967fa.accept_10_5_7_8_1_1176
  25 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 88
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 88 (accept_3_3 23 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37
  88 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 37 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 88 (accept_3_3 20 37 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 37 88 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 37 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 88
  (Polychromatic418967fa.accept_23_18_14_19_1_3436 18 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 88 (accept_3_3 17 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37
  88 (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 88 (accept_3_3 14 37 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 88 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 88
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 88 (accept_3_3 11 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37
  88 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 37 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 88 (accept_3_3 8 37 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 37 88 (Polychromatic418967fa.accept_18_7_1_16_1_578 7 37 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 88 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 37
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 88 (accept_3_3 5 37 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 88 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 37
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 88 (accept_3_3 2 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 88
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 37 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 88))))))))))))))))))))))))))))))))))))) (allB_succ 36 88 (allA_succ_of_accept 35 36 88 (accept_3_3 35 36
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 88 2 17 18 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 88
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 88 4 8 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 88 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 88 2 15 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 88 (accept_3_3 29 36 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 36 88 4 7 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 36 88 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 36 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 88 2 13 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 88 (Polychromatic418967fa.accept_14_11_8_4_1_2628
  25 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 88 4 6 9 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 88 (accept_3_3 23 36
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 88 2 11 18 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 88
  (Polychromatic418967fa.accept_16_5_4_8_1_1560 21 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 36 88 4 5 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 36 88 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 88 2 9 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 88 (accept_3_3 17 36 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 36 88 4 4 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 36 88 (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 36 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 88 2 7 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 88 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13
  36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 88 4 3 9 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 88 (accept_3_3 11 36
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 88 2 5 18 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 88
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 88 4 2 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 88 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 36 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 88 2 3 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 88 (accept_3_3 5 36 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 36 88 4 1 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 36 88 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 88 2 1 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 88 (Polychromatic418967fa.accept_16_1_4_8_1_3434 1
  36 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 88))))))))))))))))))))))))))))))))))))
  (allB_succ 35 88 (allA_of_3_1 35 35 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 88 (allA_succ_of_accept
  33 34 88 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 34 88 2 16 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 34 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 34 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 88 2 15 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 88 (accept_3_3 29 34 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 88 2 14 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 34 88 (Polychromatic418967fa.accept_19_8_15_12_1_2240 27 34 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 88 2 13 17 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 88
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 88 2 12 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 88 (accept_3_3 23 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 88
  2 11 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34
  88 (Polychromatic418967fa.accept_15_6_4_13_1_403 21 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 88 2 10 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 88 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 34 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 88 2 9 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 88 (accept_3_3 17 34 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 88 2 8 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 88 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 34 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 88 2 7 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 88 (Polychromatic418967fa.accept_12_1_10_4_1_380 13
  34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 88 2 6 17 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 88 (accept_3_3 11 34
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 88 2 5 17 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 88
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 88 2 4 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 88 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 34 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 88 2 3 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 88 (accept_3_3 5 34 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 88 2 2 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 34 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 88 2 1 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 88 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  34 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 88))))))))))))))))))))))))))))))))))
  (allB_succ 33 88 (allA_succ_of_accept 32 33 88 (accept_3_3 32 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 33 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 88 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 33 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 88 (accept_3_3 29 33 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 88 (Polychromatic418967fa.accept_9_1_6_7_1_285 28
  33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 88
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 88 (accept_3_3 26 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33
  88 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 33 88 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 33 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 88 (accept_3_3 23 33 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 33 88 11 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 33 88 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 88 (accept_3_3 20 33 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 88
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 88 (accept_3_3 17 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33
  88 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 33 88 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 88 (accept_3_3 14 33 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 33 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 88 (Polychromatic418967fa.accept_9_3_6_7_1_562 12
  33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 33 88 11 1 3 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 33 88
  (Polychromatic418967fa.accept_9_1_6_7_1_285 10 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 33 88 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 88 (accept_3_3 8 33 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 33 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 88 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 33
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 88 (accept_3_3 5 33 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 88 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 33
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 88
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 88 (accept_3_3 2 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 88
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 88))))))))))))))))))))))))))))))))) (allB_succ 32 88 (allA_of_3_1 32 32 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 31 88 (allA_succ_of_accept 30 31 88 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 31 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 88 (accept_3_3 29 31 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 88 (accept_3_3 26 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31
  88 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 88 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 88 (accept_3_3 23 31 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 88 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 31 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 88 (accept_3_3 20 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31
  88 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 88 (Polychromatic418967fa.accept_15_3_1_13_1_1672 18 31 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 88 (accept_3_3 17 31 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 88 (Polychromatic418967fa.accept_21_16_10_4_1_3433 16 31 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 15
  31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 88 (accept_3_3 14 31 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 88 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 88
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 88 (accept_3_3 11 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31
  88 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 31 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 88 (accept_3_3 8 31 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 31 88 (Polychromatic418967fa.accept_14_7_3_4_1_1816 7 31 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 88 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 88 (accept_3_3 5 31 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 88 (Polychromatic418967fa.accept_13_4_5_10_1_1247 4
  31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 88 (accept_3_3 2 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 88
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 31 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 88))))))))))))))))))))))))))))))) (allB_succ 30 88 (allA_succ_of_accept 29 30 88 (accept_3_3 29 30 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 88 2 14 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 88 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 88 2 13 15 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 88
  (Polychromatic418967fa.accept_17_8_13_3_1_3432 25 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 30 88 2 12 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 88 (accept_3_3 23 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 88
  2 11 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30
  88 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 88 2 10 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 88 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 88 2 9 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 88 (accept_3_3 17 30 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 88 2 8 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 88 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 30 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 88 2 7 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 88 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 88 2 6 15 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 88 (accept_3_3 11 30
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 88 2 5 15 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 88
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 88 2 4 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 88 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 30 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 88 2 3 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 88 (accept_3_3 5 30 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 88 2 2 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 88 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 30 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 88 2 1 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 88 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 30 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 88)))))))))))))))))))))))))))))) (allB_succ
  29 88 (allA_of_3_1 29 29 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 88 (allA_succ_of_accept 27 28 88
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 88 2 13 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 88 (Polychromatic418967fa.accept_13_12_2_10_1_2698 25 28 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 88 4 6 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 88 (accept_3_3 23 28 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 88 2 11 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 28 88 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 28 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 88 4 5 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 88 (Polychromatic418967fa.accept_13_6_2_10_1_1240
  19 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 88 2 9 14 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 88 (accept_3_3 17 28
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 88 4 4 7 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28 88
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 88 2 7 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 88 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 28 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 88 4 3 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 88 (accept_3_3 11 28 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 28 88 2 5 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 28 88 (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 28 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 88 4 2 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 88 (Polychromatic418967fa.accept_16_7_12_8_1_2450 7
  28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 88 2 3 14 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 88 (accept_3_3 5 28
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 88 4 1 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 88 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 28
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 88 2 1 14 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 88
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 28 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 88)))))))))))))))))))))))))))) (allB_succ 27 88 (allA_succ_of_accept 26 27 88 (accept_3_3 26 27 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 27
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 88
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 88 (accept_3_3 23 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27
  88 (Polychromatic418967fa.accept_13_9_1_10_1_647 22 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 27 88 (Polychromatic418967fa.accept_16_5_11_8_1_3431 21 27 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 88 (accept_3_3 20 27 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 27 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 88 (Polychromatic418967fa.accept_12_6_3_4_1_394 18
  27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 88 (accept_3_3 17 27 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 88 (Polychromatic418967fa.accept_7_2_6_4_1_29 16
  27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 88
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 88 (accept_3_3 14 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27
  88 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 27 88 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 88 (accept_3_3 11 27 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 27 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 27 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 88 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 88 (accept_3_3 8 27 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 88
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 88 (accept_3_3 5 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 88
  (Polychromatic418967fa.accept_13_4_1_10_1_693 4 27 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 27 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 88 (accept_3_3 2 27 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 27 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 27 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 88))))))))))))))))))))))))))) (allB_succ 26 88 (allA_of_3_1 26
  26 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 88 (allA_succ_of_accept 24 25 88
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 88 (accept_3_3 23 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25
  88 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 25 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 88 (accept_3_3 20 25 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 25 88 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 25 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 88 (Polychromatic418967fa.accept_15_3_10_13_1_2605
  18 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 88 (accept_3_3 17 25
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 88
  (Polychromatic418967fa.accept_15_1_10_13_1_939 16 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 25 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 25 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 88 (accept_3_3 14 25 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 25 88 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 25 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 88 (Polychromatic418967fa.accept_10_2_5_8_1_139 12
  25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 88 (accept_3_3 11 25 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 88 (Polychromatic418967fa.accept_12_10_1_4_1_392
  10 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 88 (accept_3_3 8 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 88
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 88 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 25 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 88 (accept_3_3 5 25 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 88 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 25 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 88 (accept_3_3 2 25 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 88 (Polychromatic418967fa.accept_14_1_11_4_1_3430 1
  25 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 88))))))))))))))))))))))))) (allB_succ
  24 88 (allA_succ_of_accept 23 24 88 (accept_3_3 23 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  24 88 2 11 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 24 88 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 88 4 5 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 24 88 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 88 2 9 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 88 (accept_3_3 17 24 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 88 8 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 24 88 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 88 2 7 12 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 88
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 88 4 3 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 88 (accept_3_3 11 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 88
  2 5 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 88
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 24 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 88 8 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 88 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 24 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 88 2 3 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 88 (accept_3_3 5 24 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 88 4 1 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 88 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 88 2 1 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 88 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 88)))))))))))))))))))))))) (allB_succ 23
  88 (allA_of_3_1 23 23 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 88 (allA_succ_of_accept 21 22 88
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 22 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 88 2 10 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 88 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 22 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 88 2 9 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 88 (accept_3_3 17 22 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 88 2 8 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 88 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 22 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 88 2 7 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 88 (Polychromatic418967fa.accept_12_1_10_4_1_380 13
  22 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 88 2 6 11 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 22 88 11 1 2 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 22 88 2 5 11 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 88
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 22 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 88 2 4 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 88 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 22 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 88 2 3 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 88 (accept_3_3 5 22 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 88 2 2 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 88 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 22 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 88 2 1 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 88 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 88)))))))))))))))))))))) (allB_succ 21 88
  (allA_succ_of_accept 20 21 88 (accept_3_3 20 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21
  88 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 88 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 21 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 88 (accept_3_3 17 21 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 88 (Polychromatic418967fa.accept_17_16_4_3_1_3429 16 21 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 88 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 88 (accept_3_3 14 21 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 88
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 88 (accept_3_3 11 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21
  88 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 21 88 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 21 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 88 (accept_3_3 8 21 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 21 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 21 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 88 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 88 (accept_3_3 5 21 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 88 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 21
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 88
  (Polychromatic418967fa.accept_10_3_1_8_1_132 3 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 88 (accept_3_3 2 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 88
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 88))))))))))))))))))))) (allB_succ 20 88 (allA_of_3_1 20 20 88 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 19 88 (allA_succ_of_accept 18 19 88 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 19 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 88 (accept_3_3 17 19 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 88 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 19 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 88 (accept_3_3 14 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19
  88 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 19 88 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 88 (accept_3_3 11 19 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 19 88 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 19 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 88 (accept_3_3 8 19 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 88 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7
  19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 88
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 88 (accept_3_3 5 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 88
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 19 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 88 (accept_3_3 2 19 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 88 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 88))))))))))))))))))) (allB_succ 18 88 (allA_succ_of_accept 17
  18 88 (accept_3_3 17 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 88 2 8 9 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 88
  (Polychromatic418967fa.accept_12_3_6_4_1_400 15 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 88 2 7 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 88 (Polychromatic418967fa.accept_19_13_18_12_1_3428 13 18 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 88 2 6 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 88 (accept_3_3 11 18 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 88 2 5 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 88 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 18 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 88 2 4 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 88 (Polychromatic418967fa.accept_19_7_18_12_1_3427 7
  18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 88 2 3 9 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 88 (accept_3_3 5 18
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 88 2 2 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 88 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 18
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 18 88 2 1 9 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 88
  (Polychromatic418967fa.accept_15_1_3_13_1_2548 1 18 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 88)))))))))))))))))) (allB_succ 17 88 (allA_of_3_1 17 17 88 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 88 (allA_succ_of_accept 15 16 88 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 16 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 16 88 2 7 8 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 16 88
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 16 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 16 88 4 3 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 16 88 (accept_3_3 11 16 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16 88
  2 5 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 16 88
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 16 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 16 88 8 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 16 88 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 16 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 88 2 3 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 88 (accept_3_3 5 16 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 16 88 4 1 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 16 88 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 16 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 88 2 1 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 88 (Polychromatic418967fa.accept_25_1_16_13_1_3426 1
  16 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 88)))))))))))))))) (allB_succ 15 88
  (allA_succ_of_accept 14 15 88 (accept_3_3 14 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15
  88 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 88 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 88 (accept_3_3 11 15 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 88 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 15 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 88 (Polychromatic418967fa.accept_16_9_15_8_1_3425 9
  15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 88 (accept_3_3 8 15 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 88
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 88 (accept_3_3 5 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 88
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 15 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 88 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 88 (accept_3_3 2 15 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 88))))))))))))))) (allB_succ 14 88 (allA_of_3_1 14 14 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 88 (allA_succ_of_accept 12 13 88
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 88 (accept_3_3 11 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  88 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 13 88 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 88 (accept_3_3 8 13 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 88 (Polychromatic418967fa.accept_21_7_13_4_1_2169 7 13 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 88 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 88 (accept_3_3 5 13 88
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 88 (Polychromatic418967fa.accept_16_4_13_8_1_3424 4
  13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 88 (accept_3_3 2 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 88
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 88))))))))))))) (allB_succ 12 88 (allA_succ_of_accept 11 12 88 (accept_3_3 11 12 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 88 2 5 6 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 12 88 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 88 4 2 3 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 88
  (Polychromatic418967fa.accept_13_7_12_10_1_640 7 12 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 88 2 3 6 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 88 (accept_3_3 5 12 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 88 4
  1 3 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 88
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 12 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 12 88 2 1 6 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 88 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 88)))))))))))) (allB_succ 11 88 (allA_of_3_1 11 11 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 10 88 (allA_succ_of_accept 9 10 88 (Polychromatic418967fa.accept_17_9_10_3_1_3423 9 10
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 88 2 4 5 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 88
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 10 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 88 2 3 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 88 (accept_3_3 5 10 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 88 2
  2 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 88
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 10 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 88 2 1 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 88 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 10 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 88)))))))))) (allB_succ 9 88 (allA_succ_of_accept 8 9 88 (accept_3_3 8 9
  88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 9
  88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 88
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 88 (accept_3_3 5 9 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 88
  (Polychromatic418967fa.accept_10_4_9_8_1_125 4 9 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 88 (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 9 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 88 (accept_3_3 2 9 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 9 88))))))))) (allB_succ 8 88 (allA_of_3_1 8 8 88 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 7 88 (allA_succ_of_accept 6 7 88 (Polychromatic418967fa.accept_15_6_7_13_1_1666 6 7 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 88 (accept_3_3 5 7 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 88 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 7 88
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 88
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 7 88 (accept_3_3 2 7 88 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 88
  (Polychromatic418967fa.accept_16_1_7_8_1_3422 1 7 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 7 88))))))) (allB_succ 6 88 (allA_succ_of_accept 5 6 88 (accept_3_3 5 6 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 6 88 2 2 3 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 6 88 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 88 2 1 3 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 88 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 88)))))) (allB_succ 5 88 (allA_of_3_1 5 5 88 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 88 (allA_succ_of_accept 3 4 88 (Polychromatic418967fa.accept_9_3_4_7_1_89
  3 4 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 88 2 1 2 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 88
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 88 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 88)))) (allB_succ 3 88 (allA_succ_of_accept 2 3 88 (accept_3_3 2 3 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 88 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 88))) (allB_succ 2 88 (allA_of_3_1 2 2 88 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_two 88))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


