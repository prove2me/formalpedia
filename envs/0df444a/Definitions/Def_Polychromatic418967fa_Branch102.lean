-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch102
-- name    : Polychromatic418967fa_Branch102
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:10:32.107039+00:00
-- url     : https://prove2.me/theorems/4cfe0e9b-bb3f-4d9a-bf21-a242c2591650
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

def Polychromatic418967fa.branch_102 : allB 102 102 :=
  allB_succ' 2 101 102 (Eq.refl Bool.true) (allA_succ_of_accept 1 101 102 (accept_3_4 1 101 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 102)) (allB_succ' 3 100 102 (Eq.refl Bool.true) (allA_succ_of_gcd 2 100 102 2 1 50
  51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 102
  (Polychromatic418967fa.accept_13_1_9_11_1_703 1 100 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 102))) (allB_succ' 4 99 102 (Eq.refl Bool.true) (allA_succ_of_gcd 3 99 102 3 1 33 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 102
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 99 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99 102)))) (allB_succ' 5 98 102 (Eq.refl Bool.true) (allA_succ_of_gcd 4 98
  102 2 2 49 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  98 102 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 98 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 98 102 2 1 49 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 98 102 (accept_3_4 1 98 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  102))))) (allB_succ' 6 97 102 (Eq.refl Bool.true) (allA_succ_of_accept 5 97 102 (accept_3_5 5 97 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 102 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 97 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 102 (accept_3_5 2 97 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  102 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 97 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 102)))))) (allB_succ' 7 96 102 (Eq.refl Bool.true) (allA_succ_of_gcd 6 96 102 6 1 16 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 102
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 96 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 102 2 2 48 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 96 102 3 1 32 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 96 102 2 1 48 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96 102))))))) (allB_succ' 8 95 102 (Eq.refl Bool.true) (allA_succ_of_accept
  7 95 102 (accept_3_4 7 95 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 102
  (Polychromatic418967fa.accept_9_6_5_3_1_205 6 95 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 102 (accept_3_4 4 95 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 102 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 95 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 95
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 102 (accept_3_4 1 95 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 102)))))))) (allB_succ' 9 94 102 (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 94 102 2 4 47 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 94 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 102 2 3 47 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 102 (accept_3_5 5 94 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 102 2 2 47 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 102 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 94 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 102 2 1 47 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 94
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 102))))))))) (allB_succ' 10 93 102
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 93 102 3 3 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 8 93 102 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 93 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 93 102 3 2 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 93 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 93 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 102 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 93 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 102 3 1 31 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 102
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 93 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 102 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 93 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93 102)))))))))) (allB_succ' 11 92 102 (Eq.refl Bool.true) (allA_succ_of_gcd
  10 92 102 2 5 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 92 102 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 92 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 102 2 4 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 102 (accept_3_4 7 92 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 92 102 2 3 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 92 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 92 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 102 2 2 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 92
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 102 2 1 46 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 102 (accept_3_4 1 92
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 102))))))))))) (allB_succ' 12 91 102 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 91 102 (accept_3_5 11 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 102 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 102 (accept_3_5 8 91 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 91 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 102
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 102 (accept_3_5 5 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  102 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 102 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 91 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 102 (accept_3_5 2 91 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 102)))))))))))) (allB_succ' 13 90 102 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 90 102 6 2 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 102 (Polychromatic418967fa.accept_19_11_14_7_1_4473 11 90 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 102 2 5 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 102 3 3 30 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 90 102 2 4 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 102 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 90 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 102 6 1 15 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 102
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 90 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 90 102 2 2 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 90 102 3 1 30 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 90 102 2 1 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 102 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 90 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90 102))))))))))))) (allB_succ' 14 89 102 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 89 102 (accept_3_4 13 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 102 (Polychromatic418967fa.accept_20_12_9_2_1_4472 12 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 102 (accept_3_4 10 89 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 89 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 102
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 102 (accept_3_4 7 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  102 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 102 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 89 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 102 (accept_3_4 4 89 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 102 (accept_3_4 1 89 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 102)))))))))))))) (allB_succ' 15 88 102 (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 88 102 2 7 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 88 102 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 88 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 102 2 6 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 102 (accept_3_5 11 88 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 88 102 2 5 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 88 102 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 88 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 102 2 4 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 102 (Polychromatic418967fa.accept_21_7_4_18_1_4471 7
  88 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 102 2 3 44 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 102 (accept_3_5 5 88
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 102 2 2 44 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88 102
  (Polychromatic418967fa.accept_12_3_4_6_1_434 3 88 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 102 2 1 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 88 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88 102))))))))))))))) (allB_succ' 16 87 102 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 87 102 3 5 29 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 87 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 102 3 4 29 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 102
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 87 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 87 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 102 3 3 29 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 87 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 102
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 87 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 102 3 2 29 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 87 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 102 3 1 29 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 102
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 87 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87 102)))))))))))))))) (allB_succ' 17 86 102 (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 86 102 2 8 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 86 102 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 86 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 102 2 7 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 102 (accept_3_4 13 86 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 86 102 2 6 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 86 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 86 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 86 102 2 5 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 86 102 (Polychromatic418967fa.accept_12_9_2_6_1_455 9
  86 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 102 2 4 43 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 102 (accept_3_4 7 86
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 102 2 3 43 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 86 102
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 86 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 86 102 2 2 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 86 102 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 86 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 102 2 1 43 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 102 (accept_3_4 1 86 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 102))))))))))))))))) (allB_succ' 18 85 102 (Eq.refl Bool.true) (allA_succ_of_gcd 17 85 102 17
  1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 85 102
  (Polychromatic418967fa.accept_9_7_4_3_1_204 16 85 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 85 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 102 (accept_3_5 14 85 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 85 102 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 85 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 12
  85 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 102 (accept_3_5 11 85
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 102
  (Polychromatic418967fa.accept_7_3_1_4_1_121 10 85 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 85 102 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 85 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 102 (accept_3_5 8 85 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 85 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 102 (Polychromatic418967fa.accept_9_6_4_3_1_203 6
  85 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 102 (accept_3_5 5 85 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 102 (Polychromatic418967fa.accept_13_4_7_11_1_1981
  4 85 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 102 (accept_3_5 2 85 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  102 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 85 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 85 102)))))))))))))))))) (allB_succ' 19 84 102 (Eq.refl Bool.true) (allA_succ_of_gcd 18 84 102 6 3 14 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 102
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 84 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 84 102 2 8 42 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 84 102 3 5 28 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 84 102 2 7 42 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 102 (Polychromatic418967fa.accept_16_13_4_6_1_2322 13 84 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 102 6 2 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 102 (Polychromatic418967fa.accept_16_11_4_6_1_4422 11 84 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 102 2 5 42 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 84 102 3 3 28 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 84 102 2 4 42 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 102
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 84 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 84 102 6 1 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 102 (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 84 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 102 2 2 42 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 84 102 3 1 28 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 84 102 2 1 42 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 102 (Polychromatic418967fa.accept_19_1_8_7_1_4470 1 84 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 102))))))))))))))))))) (allB_succ' 20 83 102
  (Eq.refl Bool.true) (allA_succ_of_accept 19 83 102 (accept_3_4 19 83 102 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 83 102 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 83 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 102 (accept_3_4 16 83 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 102 (Polychromatic418967fa.accept_9_6_2_3_1_771 15
  83 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 102
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 83 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 102 (accept_3_4 13 83 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 102 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 83 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 102 (accept_3_4 10 83 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 102
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 83 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 102 (accept_3_4 7 83 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  102 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 83 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 102 (accept_3_4 4 83 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 83 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 83
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 102 (accept_3_4 1 83 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83 102)))))))))))))))))))) (allB_succ' 21 82 102 (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 82 102 2 10 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 82 102 (Polychromatic418967fa.accept_11_8_5_3_1_694 19 82 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 102 2 9 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 102 (accept_3_5 17 82 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82 102 2 8 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 82 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 82 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 102 2 7 41 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 102
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 82 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 82 102 2 6 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 82 102 (accept_3_5 11 82 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82
  102 2 5 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  82 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 82 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 82 102 2 4 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 82 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 82 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 102 2 3 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 102 (accept_3_5 5 82 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 102 2 2 41 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 82 102 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 82 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 102 2 1 41 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 102
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 82 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 102))))))))))))))))))))) (allB_succ' 22 81 102 (Eq.refl Bool.true) (allA_succ_of_gcd 21 81 102 3 7 27 34
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 102
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 81 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 102 3 6 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 102 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 81 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 102
  (Polychromatic418967fa.accept_10_6_1_2_1_874 16 81 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 81 102 3 5 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 81 102 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 81 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 102 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 81 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 102 3 4 27 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 102 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 81 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 102 3 3 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 102 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 81 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 81 102 3 2 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 81 102 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 81 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 102 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 81 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 102 3 1 27 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 102
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 81 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 102 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 81 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81 102)))))))))))))))))))))) (allB_succ' 23 80 102 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 80 102 2 11 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 80 102 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 80 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 102 2 10 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 102 (accept_3_4 19 80 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 102 2 9 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 80 102 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 80 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 102 2 8 40 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 102
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 80 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 80 102 2 7 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 102 (accept_3_4 13 80 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  102 2 6 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 80 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 102 2 5 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 102 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 80 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 102 2 4 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 102 (accept_3_4 7 80 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 102 2 3 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 80 102 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 80 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 102 2 2 40 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 102
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 80 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 102 2 1 40 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 102 (accept_3_4 1 80 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  102))))))))))))))))))))))) (allB_succ' 24 79 102 (Eq.refl Bool.true) (allA_succ_of_accept 23 79 102 (accept_3_5 23 79
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 102 (Polychromatic418967fa.accept_9_4_7_3_1_43
  22 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 102 (accept_3_5 20 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 102 (Polychromatic418967fa.accept_22_18_13_14_1_4469 18 79 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 102 (accept_3_5 17 79 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 102 (Polychromatic418967fa.accept_13_3_1_11_1_1268 16 79
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 102
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 102 (accept_3_5 14 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 102 (accept_3_5 11 79 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 79 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 102 (accept_3_5 8 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  102 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 102 (accept_3_5 5 79 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 102 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 79 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 102
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 102 (accept_3_5 2 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 102)))))))))))))))))))))))) (allB_succ' 25 78 102 (Eq.refl Bool.true) (allA_succ_of_gcd 24 78 102 6 4 13
  17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 102
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 78 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 102 2 11 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 78 102 3 7 26 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 78 102 2 10 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 78 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 102 6 3 13 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 78 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 102 2 8 39 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 102 3 5 26 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 102 2 7 39 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 102
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 78 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 102 6 2 13 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 102 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 78 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 102 2 5 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 78 102 3 3 26 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 78 102 2 4 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 102 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 78 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 102 6 1 13 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 102
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 78 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 78 102 2 2 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 78 102 3 1 26 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 78 102 2 1 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 78 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78 102))))))))))))))))))))))))) (allB_succ' 26 77 102 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 77 102 (accept_3_4 25 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 102 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 102 (accept_3_4 22 77 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 102 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 77 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 102
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 102 (accept_3_4 19 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 102 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 102 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 77 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 102 (accept_3_4 16 77 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 102
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 102 (accept_3_4 13 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 102 (Polychromatic418967fa.accept_19_12_1_7_1_4468 12 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 102 (accept_3_4 10 77 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 102 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 77 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 102
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 102 (accept_3_4 7 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  102 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 77 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 102 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 77 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 102 (accept_3_4 4 77 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 77
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 102 (accept_3_4 1 77 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 102)))))))))))))))))))))))))) (allB_succ' 27 76 102 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 76 102 2 13 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 76 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 76 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 102 2 12 38 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 102 (accept_3_5 23 76 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 102 2 11 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 102 (Polychromatic418967fa.accept_10_1_6_2_1_867 21
  76 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 102 2 10 38 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 102
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 76 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 102 2 9 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 102 (accept_3_5 17 76 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  102 2 8 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 102 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 76 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 102 2 7 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 102 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 76 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 102 2 6 38 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 102 (accept_3_5 11 76 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 102 2 5 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 76 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 102 2 4 38 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 102
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 76 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 102 2 3 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 102 (accept_3_5 5 76 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 102
  2 2 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  102 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 102 2 1 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 76 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76 102))))))))))))))))))))))))))) (allB_succ' 28 75 102 (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 75 102 3 9 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 75 102 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 75 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 102 3 8 25 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 102
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 75 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 75 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 102 3 7 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 102 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 75 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 102
  (Polychromatic418967fa.accept_16_3_11_6_1_4467 19 75 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 102 3 6 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 75 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 102 3 5 25 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 102
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 75 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 102 3 4 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 102 (Polychromatic418967fa.accept_19_11_18_7_1_4466 11 75
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 102
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 75 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 75 102 3 3 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 75 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 75 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 102 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 75 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 102 3 2 25 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 102 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 75 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 102 3 1 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 75 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 102)))))))))))))))))))))))))))) (allB_succ' 29 74 102 (Eq.refl Bool.true) (allA_succ_of_gcd 28 74 102 2
  14 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74
  102 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 74 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 74 102 2 13 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 74 102 (accept_3_4 25 74 102 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 102 2 12 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 74 102 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 74 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 102 2 11 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 102 (Polychromatic418967fa.accept_12_9_2_6_1_455 21
  74 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 102 2 10 37 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 102 (accept_3_4 19
  74 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 102 2 9 37 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 102
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 74 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 74 102 2 8 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 74 102 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 74 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 102 2 7 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 102 (accept_3_4 13 74 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 74 102 2 6 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 74 102 (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 74 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 102 2 5 37 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 102
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 74 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 74 102 2 4 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 74 102 (accept_3_4 7 74 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 102
  2 3 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74
  102 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 74 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 74 102 2 2 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 74 102 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 74 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 102 2 1 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 102 (accept_3_4 1 74 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 102))))))))))))))))))))))))))))) (allB_succ' 30 73 102 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 73 102 (accept_3_5 29 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 102 (Polychromatic418967fa.accept_19_9_16_7_1_1056 28 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 102 (accept_3_5 26 73 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 73 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 102
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 102 (accept_3_5 23 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 102 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 73 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 102 (accept_3_5 20 73 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 102
  (Polychromatic418967fa.accept_15_3_13_12_1_348 18 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 102 (accept_3_5 17 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 102 (accept_3_5 14 73 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 102 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 102
  (Polychromatic418967fa.accept_19_12_16_7_1_4456 12 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 102 (accept_3_5 11 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 102 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 102 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 73 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 102 (accept_3_5 8 73 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 102
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 102 (accept_3_5 5 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  102 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 73 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 102 (accept_3_5 2 73 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 102)))))))))))))))))))))))))))))) (allB_succ' 31 72 102 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 72 102 6 5 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 72 102 (Polychromatic418967fa.accept_13_3_7_11_1_1904 29 72 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 102 2 14 36 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 102 3 9 24 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 72 102 2 13 36 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 102
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 25 72 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 102 6 4 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 102 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 72 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 102 2 11 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 72 102 3 7 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 72 102 2 10 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 19
  72 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 102 6 3 12 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 102
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 17 72 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 72 102 2 8 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 72 102 3 5 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 72 102 2 7 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 102 6 2 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 102 (Polychromatic418967fa.accept_19_11_15_7_1_3177 11 72
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 102 2 5 36 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 102 3 3 24 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 102 2 4 36 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 102
  (Polychromatic418967fa.accept_20_7_12_2_1_4465 7 72 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 102 6 1 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 102 2 2 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 102 3 1 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 102 2 1 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 102 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 72 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 102)))))))))))))))))))))))))))))))
  (allB_succ' 32 71 102 (Eq.refl Bool.true) (allA_succ_of_accept 31 71 102 (accept_3_4 31 71 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 102 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 71 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 102 (accept_3_4 28 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 102 (Polychromatic418967fa.accept_18_9_17_12_1_462 27 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 71 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 102 (accept_3_4 25 71 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 102
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 102 (accept_3_4 22 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 71 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 102 (accept_3_4 19 71 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 102 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 71 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 102 (accept_3_4 16 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 102 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 102 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 71 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 102 (accept_3_4 13 71 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 102
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 102 (accept_3_4 10 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 71 102 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 71 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 102 (accept_3_4 7 71 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 71 102 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 71 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 102 (accept_3_4 4 71 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  71 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 102
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 102 (accept_3_4 1 71 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  102)))))))))))))))))))))))))))))))) (allB_succ' 33 70 102 (Eq.refl Bool.true) (allA_succ_of_gcd 32 70 102 2 16 35 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 102
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 70 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 102 2 15 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 70 102 (accept_3_5 29 70 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70
  102 2 14 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  70 102 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 70 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 70 102 2 13 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 70 102 (Polychromatic418967fa.accept_19_6_13_7_1_4464 25 70 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 102 2 12 35 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 102 (accept_3_5 23 70 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 102 2 11 35 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 102
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 70 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 102 2 10 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 70 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 102 2 9 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 102 (accept_3_5 17 70 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 70 102 2 8 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 70 102 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 70 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 102 2 7 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 102 (Polychromatic418967fa.accept_9_4_7_3_1_43 13
  70 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 102 2 6 35 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 102 (accept_3_5 11
  70 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 102 2 5 35 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 102
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 70 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 102 2 4 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 102 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 70 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 102 2 3 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 102 (accept_3_5 5 70 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 102 2 2 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 102 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 70 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 102 2 1 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 70
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 102)))))))))))))))))))))))))))))))))
  (allB_succ' 34 69 102 (Eq.refl Bool.true) (allA_succ_of_gcd 33 69 102 3 11 23 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 102
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 69 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 102 3 10 23 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 102 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  69 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 102
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 69 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 69 102 3 9 23 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 69 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 102 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 69 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 102 3 8 23 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 69 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 102 3 7 23 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 102 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 69 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 102 3 6 23 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 69 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 69 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 102 3 5 23 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 102
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 69 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 69 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 102 3 4 23 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 102
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 69 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 102 3 3 23 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 102 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 69 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 102 3 2 23 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 102
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 69 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 102 3 1 23 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 69 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 102
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 69 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 102)))))))))))))))))))))))))))))))))) (allB_succ' 35 68 102 (Eq.refl Bool.true) (allA_succ_of_gcd 34 68
  102 34 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  68 102 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 68 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 68 102 2 16 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 68 102 (accept_3_4 31 68 102 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 68 102 2 15 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 68 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 68 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 102 2 14 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 102 (Polychromatic418967fa.accept_7_6_5_4_1_297 27
  68 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 102 2 13 34 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 102 (accept_3_4 25
  68 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 102 2 12 34 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 102
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 68 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 68 102 2 11 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 68 102 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 68 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 102 2 10 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 102 (accept_3_4 19 68 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 102 2 9 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 17 68 102 17 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 68 102 2 8 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 68 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 68 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 102 2 7 34 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 102 (accept_3_4 13 68 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 102 2 6 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 68 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 102 2 5 34 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 102
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 68 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 102 2 4 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 102 (accept_3_4 7 68 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 102
  2 3 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  102 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 102 2 2 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 102 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 68 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 102 2 1 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 102 (accept_3_4 1 68 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 102))))))))))))))))))))))))))))))))))) (allB_succ' 36 67 102 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 67 102 (accept_3_5 35 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 102 (accept_3_5 32 67 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 102 (Polychromatic418967fa.accept_22_9_1_14_1_4463 31 67 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 102
  (Polychromatic418967fa.accept_13_4_2_11_1_733 30 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 102 (accept_3_5 29 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 102 (Polychromatic418967fa.accept_16_11_3_6_1_4462 27 67 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 102 (accept_3_5 26 67 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 102
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 102 (accept_3_5 23 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 102 (Polychromatic418967fa.accept_13_9_2_11_1_1964 22 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 102 (accept_3_5 20 67 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 67 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 102
  (Polychromatic418967fa.accept_15_3_7_12_1_372 18 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 102 (accept_3_5 17 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 102 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 67 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 102 (accept_3_5 14 67 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 102
  (Polychromatic418967fa.accept_20_12_7_2_1_4448 12 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 102 (accept_3_5 11 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 102 (accept_3_5 8 67 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 67 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 102
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 102 (accept_3_5 5 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  102 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 67 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 102 (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 67 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 102 (accept_3_5 2 67 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 102)))))))))))))))))))))))))))))))))))) (allB_succ' 37 66 102
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 66 102 6 6 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 66 102 (Polychromatic418967fa.accept_13_9_1_11_1_275 35 66 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 102 2 17 33 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 102 3 11 22 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 102 2 16 33 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 102
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 66 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 102 6 5 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 66 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 102 2 14 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 66 102 3 9 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 66 102 2 13 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 102 (Polychromatic418967fa.accept_13_12_1_11_1_1917
  25 66 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 102 6 4 11 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 102
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 66 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 102 2 11 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 66 102 3 7 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 66 102 2 10 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 102 (Polychromatic418967fa.accept_16_3_2_6_1_4461 19 66 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 102 6 3 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 102 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 66 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 102 2 8 33 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 102 3 5 22 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 102 2 7 33 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 102
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 66 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 102 6 2 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 102 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 66 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 102 2 5 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 66 102 3 3 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 66 102 2 4 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 102 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 66 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 102 6 1 11 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 102
  (Polychromatic418967fa.accept_15_5_6_12_1_916 5 66 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 102 2 2 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 66 102 3 1 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 66 102 2 1 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 66 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 102))))))))))))))))))))))))))))))))))))) (allB_succ' 38 65 102 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 65 102 (accept_3_4 37 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 65 102 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 65 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 102 (accept_3_4 34 65 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 102
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 102 (accept_3_4 31 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 102 (Polychromatic418967fa.accept_14_2_9_4_1_1735 30 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 102 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 65 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 102 (accept_3_4 28 65 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 102
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 102 (accept_3_4 25 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 102 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 102 (accept_3_4 22 65 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 102 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 65 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 102
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 102 (accept_3_4 19 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 102 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 102 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 65 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 102 (accept_3_4 16 65 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 102
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 102 (accept_3_4 13 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 102 (accept_3_4 10 65 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 102 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 65 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 102
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 102 (accept_3_4 7 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  102 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 102 (accept_3_4 4 65 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 102 (Polychromatic418967fa.accept_14_2_9_4_1_1735 2
  65 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 102 (accept_3_4 1 65 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 102)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 64 102
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 64 102 2 19 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 64 102 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 64 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 102 2 18 32 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 102 (accept_3_5 35 64 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 102 2 17 32 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 102
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 64 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 64 102 2 16 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 64 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 64 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 102 2 15 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 102 (accept_3_5 29 64 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 102 2 14 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 102 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 64 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 102 2 13 32 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 102
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 64 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 102 2 12 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 102 (accept_3_5 23 64 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  102 2 11 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  64 102 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 64 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 102 2 10 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 64 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 64 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 102 2 9 32 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 102 (accept_3_5 17 64 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 102 2 8 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 64 102 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 64 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 102 2 7 32 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 102
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 64 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 102 2 6 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 102 (accept_3_5 11 64 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  102 2 5 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 102 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 64 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 102 2 4 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 64 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 102 2 3 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 102 (accept_3_5 5 64 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 102 2 2 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 64 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 102 2 1 32 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 102
  (Polychromatic418967fa.accept_13_1_12_11_1_728 1 64 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 102))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 63 102 (Eq.refl Bool.true) (allA_succ_of_gcd 39
  63 102 3 13 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  38 63 102 (Polychromatic418967fa.accept_11_5_8_3_1_66 38 63 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 63 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 102 3 12 21 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 102
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 63 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 102 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 63 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 102 3 11 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 102 (Polychromatic418967fa.accept_12_8_3_6_1_909 32
  63 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 102
  (Polychromatic418967fa.accept_10_1_3_2_1_220 31 63 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 102 3 10 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 102 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 63 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 102 3 9 21 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 102
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 63 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 102 3 8 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 102 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 63 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 102
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 63 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 102 3 7 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 102 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 63 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 102 (Polychromatic418967fa.accept_20_19_3_2_1_3118 19 63
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 102 3 6 21 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 102 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 63 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 102 3 5 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 102 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 63 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 102 3 4 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 102 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 63 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 102 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 63 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 102 3 3 21 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 102
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 63 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 102 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 63 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 102 3 2 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 102
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 63 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 102 3 1 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 102 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 63 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 102))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 62 102 (Eq.refl Bool.true) (allA_succ_of_gcd 40 62 102 2 20 31 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 102
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 62 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 102 2 19 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 62 102 (accept_3_4 37 62 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62
  102 2 18 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  62 102 (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 62 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 62 102 2 17 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 62 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 62 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 62 102 2 16 31 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 62 102 (accept_3_4 31 62 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62 102 2 15 31 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 62 102
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 62 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 62 102 2 14 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 62 102 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 62 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 102 2 13 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 102 (accept_3_4 25 62 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 102 2 12 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 62 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 102 2 11 31 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 102
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 62 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 102 2 10 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 62 102 (accept_3_4 19 62 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62
  102 2 9 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  62 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 62 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 62 102 2 8 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 62 102 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 62 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 102 2 7 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 102 (accept_3_4 13 62 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 102 2 6 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 62 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 62 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 62 102 2 5 31 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 62 102
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 62 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 62 102 2 4 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 62 102 (accept_3_4 7 62 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 102
  2 3 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 62
  102 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 62 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 62 102 2 2 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 62 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 62 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 102 2 1 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 102 (accept_3_4 1 62 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 102))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 61 102 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 61 102 (accept_3_5 41 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 102 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 102 (accept_3_5 38 61 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 102
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 102 (accept_3_5 35 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 102 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 102 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 61 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 102 (accept_3_5 32 61 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 102
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 102 (accept_3_5 29 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 102 (accept_3_5 26 61 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 102 (Polychromatic418967fa.accept_16_9_13_6_1_2334 25 61 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 102
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 102 (accept_3_5 23 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 102 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 61 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 102 (accept_3_5 20 61 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 102
  (Polychromatic418967fa.accept_23_18_15_10_1_4460 18 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 61 102 (accept_3_5 17 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 61 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 61 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 102 (accept_3_5 14 61 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 102 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 102
  (Polychromatic418967fa.accept_19_12_4_7_1_4459 12 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 102 (accept_3_5 11 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 61 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 102 (accept_3_5 8 61 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 102
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 102 (accept_3_5 5 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  102 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 61 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 102 (accept_3_5 2 61 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 102)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 60
  102 (Eq.refl Bool.true) (allA_succ_of_gcd 42 60 102 6 7 10 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 60 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 102 2 20 30 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 102 3 13 20 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 60 102 2 19 30 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 102
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 60 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 102 6 6 10 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 60 102 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 60 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 102 2 17 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 60 102 3 11 20 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 60 102 2 16 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 31
  60 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 102 6 5 10 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 102
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 60 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 60 102 2 14 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 60 102 3 9 20 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 60 102 2 13 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 60 102 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 60 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 102 6 4 10 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 60 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 102 2 11 30 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 102 3 7 20 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 102 2 10 30 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 102
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 60 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 102 6 3 10 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 102 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 60 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 102 2 8 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 102 3 5 20 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 102 2 7 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 60 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 102 6 2 10 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 102
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 60 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 102 2 5 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 60 102 3 3 20 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 60 102 2 4 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 102 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 60 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 102 6 1 10 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 60 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 102 2 2 30 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 102 3 1 20 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 102 2 1 30 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 102
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 60 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 102))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 59 102 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 59 102 (accept_3_4 43 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 102 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 102 (accept_3_4 40 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 102 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 59 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 102
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 102 (accept_3_4 37 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 102 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 102 (accept_3_4 34 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 102
  (Polychromatic418967fa.accept_15_2_14_12_1_2453 32 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 102 (accept_3_4 31 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 102 (Polychromatic418967fa.accept_13_4_7_11_1_1981 30 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 102 (accept_3_4 28 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 102 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 59 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 102
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 102 (accept_3_4 25 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 102 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 102 (Polychromatic418967fa.accept_19_4_2_7_1_4458 23 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 102 (accept_3_4 22 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 102
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 102 (accept_3_4 19 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 102 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 102 (accept_3_4 16 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 59 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 102
  (Polychromatic418967fa.accept_13_1_7_11_1_702 14 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 102 (accept_3_4 13 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 102 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 102 (accept_3_4 10 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 102
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 102 (accept_3_4 7 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  102 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 59 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 102 (accept_3_4 4 59 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 102 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 59 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 59
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 102 (accept_3_4 1 59 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 102)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  58 102 (Eq.refl Bool.true) (allA_succ_of_gcd 44 58 102 2 22 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 58 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 102 2 21 29 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 102 (accept_3_5 41
  58 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 102 2 20 29 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 102
  (Polychromatic418967fa.accept_12_3_10_6_1_442 39 58 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 102 2 19 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 58 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 102 2 18 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 102 (accept_3_5 35 58 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 102 2 17 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 58 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 102 2 16 29 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 102
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 31 58 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 102 2 15 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 102 (accept_3_5 29 58 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  102 2 14 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 58 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 102 2 13 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 58 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 102 2 12 29 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 102 (accept_3_5 23 58 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 102 2 11 29 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 102
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 58 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 102 2 10 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 58 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 102 2 9 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 102 (accept_3_5 17 58 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 102 2 8 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 102 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 58 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 102 2 7 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  58 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 102 2 6 29 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 102 (accept_3_5 11
  58 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 102 2 5 29 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 102
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 58 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 102 2 4 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 58 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 102 2 3 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 102 (accept_3_5 5 58 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 102 2 2 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 102 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 58 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 102 2 1 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 58
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  102))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 57 102 (Eq.refl Bool.true) (allA_succ_of_gcd 45 57 102
  3 15 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57
  102 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 57 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 102 3 14 19 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 102
  (Polychromatic418967fa.accept_21_20_15_18_1_4457 41 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 57 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 102 3 13 19 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 102
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 102 (Polychromatic418967fa.accept_18_1_3_12_1_467 37 57 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 102 3 12 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 102
  (Polychromatic418967fa.accept_10_4_7_2_1_211 34 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 102 3 11 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 102 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 57 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 102 3 10 19 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 102
  (Polychromatic418967fa.accept_10_9_7_2_1_887 29 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 102 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 57 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 102 3 9 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 57 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 102
  (Polychromatic418967fa.accept_10_5_7_2_1_516 25 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 102 3 8 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 102 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 57
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 102 3 7 19 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 102
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 102 3 6 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 102
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 102 3 5 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 102 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 57 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 102 (Polychromatic418967fa.accept_16_13_9_6_1_2306 13 57
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 102 3 4 19 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 57 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 102 3 3 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 102 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 57 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 102 3 2 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 102 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 57 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 102 3 1 19 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 102
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 57 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 102 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 57 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 102)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 56 102
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 56 102 2 23 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 56 102 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 56 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 102 2 22 28 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 102 (accept_3_4 43 56 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 102 2 21 28 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 102
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 56 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 56 102 2 20 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 56 102 (Polychromatic418967fa.accept_12_3_8_6_1_895 39 56 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 102 2 19 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 102 (accept_3_4 37 56 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 102 2 18 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 56 102 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 56 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 102 2 17 28 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 102
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 56 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 102 2 16 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 102 (accept_3_4 31 56 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  102 2 15 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  56 102 (Polychromatic418967fa.accept_15_14_11_12_1_4440 29 56 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 102 2 14 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 56 102 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 56 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 102 2 13 28 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 102 (accept_3_4 25 56 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 102 2 12 28 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 102
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 56 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 56 102 2 11 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 56 102 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 56 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 102 2 10 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 102 (accept_3_4 19 56 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 102 2 9 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 56 102 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 56 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 102 2 8 28 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 102
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 56 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 102 2 7 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 102 (accept_3_4 13 56 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56
  102 2 6 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  56 102 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 102 2 5 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 102 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 56 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 102 2 4 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 102 (accept_3_4 7 56 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 102 2 3 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 56 102 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 56 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 102 2 2 28 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 102
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 56 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 102 2 1 28 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 102 (accept_3_4 1 56 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  102))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 55 102 (Eq.refl Bool.true) (allA_succ_of_accept 47
  55 102 (accept_3_5 47 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 102
  (Polychromatic418967fa.accept_13_7_3_11_1_280 46 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 55 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 102 (accept_3_5 44 55 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 55 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 102 (Polychromatic418967fa.accept_9_6_1_3_1_191 42
  55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 102 (accept_3_5 41 55
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 102
  (Polychromatic418967fa.accept_7_5_6_4_1_117 40 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 55 102 (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 55 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 102 (accept_3_5 38 55 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 55 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 102
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 102 (accept_3_5 35 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 102 (accept_3_5 32 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 102
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 102 (accept_3_5 29 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 102 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 102 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 102 (accept_3_5 26 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 102
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 102 (accept_3_5 23 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 102 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 102 (accept_3_5 20 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 102
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 102 (accept_3_5 17 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 102 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 102 (accept_3_5 14 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 102
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 102 (accept_3_5 11 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 102 (accept_3_5 8 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 55 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 102
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 102 (accept_3_5 5 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  102 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 55 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 55 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 102 (accept_3_5 2 55 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 102)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  49 54 102 (Eq.refl Bool.true) (allA_succ_of_gcd 48 54 102 6 8 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 102 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 54 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 102 2 23 27 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 54 102 3 15 18 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 54 102 2 22 27 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 102
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 54 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 102 6 7 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 102 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 54 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 102 2 20 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 54 102 3 13 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 54 102 2 19 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 37
  54 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 102 6 6 9 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 102
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 54 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 102 2 17 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 54 102 3 11 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 54 102 2 16 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 102 (Polychromatic418967fa.accept_19_12_16_7_1_4456 31 54 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 102 6 5 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 54 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 102 2 14 27 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 102 3 9 18 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 102 2 13 27 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 102
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 54 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 102 6 4 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 54 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 102 2 11 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 102 3 7 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 54 102 2 10 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 102 (Polychromatic418967fa.accept_15_4_9_12_1_2495
  19 54 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 102 6 3 9 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 102
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 54 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 54 102 2 8 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 54 102 3 5 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 54 102 2 7 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 102 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 54 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 102 6 2 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 102 (Polychromatic418967fa.accept_21_11_12_18_1_4455 11 54
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 102 2 5 27 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 102 3 3 18 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 102 2 4 27 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 102
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 54 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 102 6 1 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 102 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 54 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 102 2 2 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 102 3 1 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 102 2 1 27 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 54 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  102))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 53 102 (Eq.refl Bool.true) (allA_succ_of_accept 49
  53 102 (accept_3_4 49 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 102
  (Polychromatic418967fa.accept_13_9_1_11_1_275 48 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 53 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 53 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 102 (accept_3_4 46 53 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 53 102 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 102 (Polychromatic418967fa.accept_25_19_3_2_1_4454
  44 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 102 (accept_3_4 43
  53 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 102
  (Polychromatic418967fa.accept_9_6_8_3_1_183 42 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 53 102 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 53 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 102 (accept_3_4 40 53 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 53 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 38
  53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 102 (accept_3_4 37 53
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 102
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 53 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 102 (accept_3_4 34 53 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 53 102 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 102 (Polychromatic418967fa.accept_9_5_8_3_1_437 32
  53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 102 (accept_3_4 31 53
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 102
  (Polychromatic418967fa.accept_19_11_15_7_1_3177 30 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 53 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 53 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 102 (accept_3_4 28 53 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 53 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 102
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 102 (accept_3_4 25 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 102 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 102 (accept_3_4 22 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 102 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 53 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 102
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 102 (accept_3_4 19 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 102 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 102 (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 102 (accept_3_4 16 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 102
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 102 (accept_3_4 13 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 102 (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 102 (accept_3_4 10 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 102 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 53 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 102
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 102 (accept_3_4 7 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  102 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 102 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 53 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 102 (accept_3_4 4 53 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  53 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 102 (accept_3_4 1 53 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 102))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 52 102 (Eq.refl Bool.true) (allA_succ_of_gcd 50 52 102 2 25 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 102
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 52 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 52 102 2 24 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 52 102 (accept_3_5 47 52 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52
  102 2 23 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  52 102 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 52 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 52 102 2 22 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 52 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 52 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 102 2 21 26 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 102 (accept_3_5 41 52 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 102 2 20 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 102
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 52 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 52 102 2 19 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 52 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 52 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 102 2 18 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 102 (accept_3_5 35 52 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 102 2 17 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 102 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 52 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 102 2 16 26 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 102
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 52 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 102 2 15 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 102 (accept_3_5 29 52 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  102 2 14 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 102 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 102 2 13 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 102 (Polychromatic418967fa.accept_15_10_7_12_1_2490 25 52 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 102 2 12 26 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 102 (accept_3_5 23 52 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 102 2 11 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 102
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 52 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 52 102 2 10 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 52 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 52 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 102 2 9 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 102 (accept_3_5 17 52 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 52 102 2 8 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 52 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 52 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 102 2 7 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 102 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  52 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 102 2 6 26 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 102 (accept_3_5 11
  52 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 102 2 5 26 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 102
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 52 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 102 2 4 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 102 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 52 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 102 2 3 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 102 (accept_3_5 5 52 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 102 2 2 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 102 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 52 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 102 2 1 26 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 52
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  102))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 102 (allA_succ_of_accept 50 51 102
  (Polychromatic418967fa.accept_9_5_6_3_1_40 50 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 102 3 16 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 47
  51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 102
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 102 3 15 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 102 (Polychromatic418967fa.accept_9_8_6_3_1_457 44 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 102 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 51 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 102 3 14 17 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 102 3 13 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 102 (Polychromatic418967fa.accept_9_2_6_3_1_178 38
  51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 102 3 12 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 102 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 51 102 17 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 51 102 3 11 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 51 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 102
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 102 3 10 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 51 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 102 3 9 17 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 102
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 102 3 8 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 51 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 102
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 102 3 7 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 51 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 102 3 6 17 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 17 51 102 17 1 3 6 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 51 102
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 102 3 5 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 102 3 4 17 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 102
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 102 3 3 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 102 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 51 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 102
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 102 3 2 17 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 51 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 102 3 1 17 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 102
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 51 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 102))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 102
  (allA_succ_of_accept 49 50 102 (accept_3_4 49 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50
  102 2 24 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  50 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 50 102 2 23 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 50 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 50 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 102 2 22 25 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 102 (accept_3_4 43 50 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 102 2 21 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 102
  (Polychromatic418967fa.accept_11_8_6_3_1_661 41 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 102 2 20 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 102 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 50 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 102 2 19 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 102 (accept_3_4 37 50 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 102 2 18 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 102 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 50 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 102 2 17 25 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 102
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 102 2 16 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 102 (accept_3_4 31 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  102 2 15 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 102 2 14 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 102 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 50 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 102 2 13 25 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 102 (accept_3_4 25 50 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 102 2 12 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 102
  (Polychromatic418967fa.accept_15_8_5_12_1_4453 23 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 102 2 11 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 102 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 50 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 102 2 10 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 102 (accept_3_4 19 50 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 102 2 9 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 50 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 102 2 8 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 102
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 102 2 7 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 102 (accept_3_4 13 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  102 2 6 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 102 2 5 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 102 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 50 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 102 2 4 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 102 (accept_3_4 7 50 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 102 2 3 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 50 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 102 2 2 25 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 102
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 102 2 1 25 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 102 (accept_3_4 1 50 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  102)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 102 (allA_succ_of_accept 48 49 102
  (Polychromatic418967fa.accept_21_6_7_18_1_1783 48 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 102 (accept_3_5 47 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 102 (Polychromatic418967fa.accept_14_3_7_4_1_118 45 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 102 (accept_3_5 44 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 49 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 102
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 102 (accept_3_5 41 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 102 (Polychromatic418967fa.accept_13_1_10_11_1_1280 40 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 102 (accept_3_5 38 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 49 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 102
  (Polychromatic418967fa.accept_21_15_7_18_1_4452 36 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 102 (accept_3_5 35 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 102 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 102 (accept_3_5 32 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 102
  (Polychromatic418967fa.accept_11_8_5_3_1_694 30 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 102 (accept_3_5 29 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 102 (accept_3_5 26 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 49 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 102
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 102 (accept_3_5 23 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 102 (Polychromatic418967fa.accept_15_7_4_12_1_2530 22 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 102 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 102 (accept_3_5 20 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 102
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 18 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 102 (accept_3_5 17 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 102 (accept_3_5 14 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 102 (Polychromatic418967fa.accept_19_13_11_7_1_4451 13 49 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 102
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 49 102 (accept_3_5 11 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 49 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 49 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 102 (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 49 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 102 (accept_3_5 8 49 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 102
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 102 (accept_3_5 5 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  102 (Polychromatic418967fa.accept_13_4_10_11_1_1908 4 49 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 102 (accept_3_5 2 49 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 49 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 102)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 102 (allA_succ_of_accept 47 48 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 48 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 102 2 23 24 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 48 102 3 15 16 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 48 102 2 22 24 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 102
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 48 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 102 6 7 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 102 (Polychromatic418967fa.accept_13_2_9_11_1_258 41 48 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 102 2 20 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 102 3 13 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 102 2 19 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 37
  48 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 102 6 6 8 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 102
  (Polychromatic418967fa.accept_10_5_8_2_1_517 35 48 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 102 2 17 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 48 102 3 11 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 48 102 2 16 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 102 6 5 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 102 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 48 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 102 2 14 24 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 48 102 3 9 16 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 48 102 2 13 24 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 102
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 48 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 102 6 4 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 102 2 11 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 102 3 7 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 102 2 10 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 19
  48 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 102 6 3 8 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 102
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 48 102 2 8 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 48 102 3 5 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 48 102 2 7 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 102 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 48 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 102 6 2 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 102 (Polychromatic418967fa.accept_21_11_6_18_1_4450 11 48
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 102 2 5 24 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 102 3 3 16 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 102 2 4 24 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 102
  (Polychromatic418967fa.accept_11_7_4_3_1_302 7 48 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 102 6 1 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 102 2 2 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 102 3 1 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 102 2 1 24 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 102 (Polychromatic418967fa.accept_13_1_9_11_1_703 1 48 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  102)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 102 (allA_succ_of_accept 46 47 102 (accept_3_4 46 47
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 102 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 102
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 102 (accept_3_4 43 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 102 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 102 (accept_3_4 40 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 102 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 47 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 102
  (Polychromatic418967fa.accept_20_18_7_2_1_4449 38 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 102 (accept_3_4 37 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 102 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 102 (accept_3_4 34 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 102
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 102 (accept_3_4 31 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 102 (accept_3_4 28 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 102 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 47 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 102
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 102 (accept_3_4 25 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 102 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 102 (accept_3_4 22 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 102
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 102 (accept_3_4 19 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 102 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 102 (accept_3_4 16 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 102
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 102 (accept_3_4 13 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 102 (Polychromatic418967fa.accept_20_12_7_2_1_4448 12 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 102 (Polychromatic418967fa.accept_19_11_9_7_1_4447 11 47 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 102 (accept_3_4 10 47 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 102
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 102 (accept_3_4 7 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  102 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 102 (accept_3_4 4 47 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 102 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 47 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  47 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 102 (accept_3_4 1 47 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 102))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  102 (allA_succ_of_accept 45 46 102 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 46 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 46 102 2 22 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 46 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 43
  46 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 102 2 21 23 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 102 (accept_3_5 41
  46 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 102 2 20 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 102
  (Polychromatic418967fa.accept_12_3_10_6_1_442 39 46 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 102 2 19 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 46 102 (Polychromatic418967fa.accept_19_18_8_7_1_4446 37 46 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 102 2 18 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 102 (accept_3_5 35 46 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 102 2 17 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 102 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 46 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 102 2 16 23 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 102
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 46 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 102 2 15 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 46 102 (accept_3_5 29 46 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46
  102 2 14 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  46 102 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 46 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 46 102 2 13 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 46 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 46 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 102 2 12 23 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 102 (accept_3_5 23 46 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 102 2 11 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 102
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 46 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 102 2 10 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 102 (Polychromatic418967fa.accept_15_4_1_12_1_914 19 46 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 102 2 9 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 102 (accept_3_5 17 46 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 102 2 8 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 102 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 46 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 102 2 7 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 102 (Polychromatic418967fa.accept_9_4_1_3_1_190 13
  46 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 102 2 6 23 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 102 (accept_3_5 11
  46 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 102 2 5 23 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 102
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 46 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 102 2 4 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 46 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 102 2 3 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 102 (accept_3_5 5 46 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 102 2 2 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 102 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 46 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 102 2 1 23 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 102 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  46 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  102)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 102 (allA_succ_of_accept 44 45 102
  (Polychromatic418967fa.accept_12_8_9_6_1_127 44 45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 102 3 14 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 102 (Polychromatic418967fa.accept_7_6_3_4_1_294 41
  45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 102
  (Polychromatic418967fa.accept_12_4_9_6_1_440 40 45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 102 3 13 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 102 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 45 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 102 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 45 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 102 3 12 15 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 102 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 45 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 102 3 11 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 102 (Polychromatic418967fa.accept_12_8_9_6_1_127 32
  45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 102 3 10 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 45 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 102 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 45 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 102 3 9 15 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 102
  (Polychromatic418967fa.accept_12_2_9_6_1_439 26 45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 102 (Polychromatic418967fa.accept_16_9_13_6_1_2334 25 45 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 102 3 8 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 102
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 102 3 7 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 102 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 45 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 102 3 6 15 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 102
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 102 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 45 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 102 3 5 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 102 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 45 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 102
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 102 3 4 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 102 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 45
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 102 3 3 15 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 102
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 102 3 2 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 102 (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 45 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 102
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 45 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 102 3 1 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 102 (Polychromatic418967fa.accept_11_2_1_3_1_683 2 45 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 45 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  102))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 102 (allA_succ_of_accept 43 44 102 (accept_3_4 43 44
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 102 2 21 22 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 102
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 44 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 102 2 20 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 102 (Polychromatic418967fa.accept_12_3_8_6_1_895 39 44 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 102 2 19 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 102 (accept_3_4 37 44 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 102 2 18 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 102 (Polychromatic418967fa.accept_19_16_6_7_1_4425 35 44 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 102 2 17 22 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 102
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 44 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 102 2 16 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 102 (accept_3_4 31 44 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  102 2 15 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 44 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 102 2 14 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 44 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 44 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 102 2 13 22 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 102 (accept_3_4 25 44 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 102 2 12 22 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 102
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 44 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 102 2 11 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 102 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 44 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 102 2 10 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 102 (accept_3_4 19 44 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 102 2 9 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 44 102 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 44 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 102 2 8 22 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 102
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 44 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 102 2 7 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 102 (accept_3_4 13 44 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  102 2 6 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 44 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 102 2 5 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 102 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 44 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 102 2 4 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 102 (accept_3_4 7 44 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 102 2 3 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 44 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 102 2 2 22 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 102
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 44 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 102 2 1 22 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 102 (accept_3_4 1 44 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  102)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 102 (allA_succ_of_accept 42 43 102
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 102 (accept_3_5 41 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 102 (Polychromatic418967fa.accept_14_11_1_4_1_4445 39 43 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 102 (accept_3_5 38 43 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 102
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 102 (accept_3_5 35 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 102 (Polychromatic418967fa.accept_13_8_4_11_1_3469 34 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 102 (accept_3_5 32 43 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 102
  (Polychromatic418967fa.accept_20_10_3_2_1_4444 30 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 102 (accept_3_5 29 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 102 (Polychromatic418967fa.accept_30_27_13_12_1_4443 27 43 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 102 (accept_3_5 26 43 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 102
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 102 (accept_3_5 23 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 102 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 102 (accept_3_5 20 43 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 102
  (Polychromatic418967fa.accept_11_7_10_3_1_633 18 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 102 (accept_3_5 17 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 102 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 102 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 43 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 102 (accept_3_5 14 43 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 102
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 102 (accept_3_5 11 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 102 (accept_3_5 8 43 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 102 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 43 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 102
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 102 (accept_3_5 5 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  102 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 43 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 43 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 102 (accept_3_5 2 43 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 102))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 102
  (allA_succ_of_accept 41 42 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 42 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 102 2 20 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 102 3 13 14 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 102 2 19 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 37
  42 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 102 6 6 7 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 102
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 42 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 102 2 17 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 42 102 3 11 14 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 42 102 2 16 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 42 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 102 6 5 7 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 102 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 42 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 102 2 14 21 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 102 3 9 14 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 102 2 13 21 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 102
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 42 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 102 6 4 7 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 42 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 102 2 11 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 102 3 7 14 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 102 2 10 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 19
  42 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 102 6 3 7 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 102
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 42 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 102 2 8 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 102 3 5 14 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 102 2 7 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 42 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 102 6 2 7 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 102 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 42 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 102 2 5 21 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 102 3 3 14 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 102 2 4 21 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 102
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 42 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 102 6 1 7 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 42 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 102 2 2 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 102 3 1 14 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 102 2 1 21 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 42 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  102)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 102 (allA_succ_of_accept 40 41 102 (accept_3_4 40 41 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 102
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 102 (accept_3_4 37 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 102 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 102 (accept_3_4 34 41 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 41 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 102
  (Polychromatic418967fa.accept_19_13_3_7_1_4423 32 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 102 (accept_3_4 31 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 41 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 102 (accept_3_4 28 41 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 102
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 102 (accept_3_4 25 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 102 (accept_3_4 22 41 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 102 (Polychromatic418967fa.accept_35_21_6_32_1_4442 21 41 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 102
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 102 (accept_3_4 19 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 102 (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 102 (accept_3_4 16 41 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 102
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 41 102 (accept_3_4 13 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 41 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 102 (accept_3_4 10 41 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 102
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 102 (accept_3_4 7 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  102 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 41 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 102 (accept_3_4 4 41 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 41
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 102 (accept_3_4 1 41 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 102))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 102
  (allA_succ_of_accept 39 40 102 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 40 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 102 2 19 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 37
  40 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 102 2 18 20 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 102 (accept_3_5 35
  40 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 102 2 17 20 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 102
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 40 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 40 102 2 16 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 40 102 (Polychromatic418967fa.accept_25_6_15_2_1_4439 31 40 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 102 2 15 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 102 (accept_3_5 29 40 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 102 2 14 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40 102 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 102 2 13 20 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 102
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 40 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 40 102 2 12 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 40 102 (accept_3_5 23 40 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40
  102 2 11 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  40 102 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 40 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 40 102 2 10 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 40 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 40 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 102 2 9 20 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 102 (accept_3_5 17 40 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 102 2 8 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 40 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 40 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 102 2 7 20 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 102
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 40 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 102 2 6 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 102 (accept_3_5 11 40 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  102 2 5 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  40 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 40 102 2 4 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 40 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 40 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 102 2 3 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 102 (accept_3_5 5 40 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 102 2 2 20 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 40 102 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 40 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 102 2 1 20 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 102
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 40 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 102)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 102 (allA_succ_of_accept 38 39 102
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 39 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 102 3 12 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 102 (Polychromatic418967fa.accept_14_7_11_4_1_3455
  35 39 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 102
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 39 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 102 3 11 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 102 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 39 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 102 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 39 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 102 3 10 13 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 102 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 39 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 102 3 9 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 102 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 39 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 102 3 8 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 102 (Polychromatic418967fa.accept_19_4_1_7_1_4438 23 39 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 102 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 39 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 102 3 7 13 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 102
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 39 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 102 (Polychromatic418967fa.accept_11_8_6_3_1_661 19 39 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 102 3 6 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 102
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 39 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 102 3 5 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 102 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 39 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 102 3 4 13 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 102
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 39 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 102 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 39 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 102 3 3 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 102 (Polychromatic418967fa.accept_11_8_6_3_1_661 8 39 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 102
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 39 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 102 3 2 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 102 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 39 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 102 3 1 13 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 102
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 39 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 102))))))))))))))))))))))))))))))))))))))) (allB_succ 38 102
  (allA_succ_of_accept 37 38 102 (accept_3_4 37 38 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  102 2 18 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 102 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 38 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 102 2 17 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 102 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 38 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 102 2 16 19 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 102 (accept_3_4 31 38 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 102 2 15 19 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 102
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 38 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 102 2 14 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 102 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 38 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 102 2 13 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 102 (accept_3_4 25 38 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 102 2 12 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 102 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 38 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 102 2 11 19 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 102
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 38 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 102 2 10 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 102 (accept_3_4 19 38 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  102 2 9 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 102 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 38 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 102 2 8 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 38 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 102 2 7 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 102 (accept_3_4 13 38 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 102 2 6 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 102 (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 38 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 102 2 5 19 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 102
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 38 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 102 2 4 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 102 (accept_3_4 7 38 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 102
  2 3 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  102 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 38 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 102 2 2 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 102 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 38 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 102 2 1 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 102 (accept_3_4 1 38 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 102)))))))))))))))))))))))))))))))))))))) (allB_succ 37 102 (allA_succ_of_accept 36 37 102
  (Polychromatic418967fa.accept_15_6_7_12_1_869 36 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 102 (accept_3_5 35 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 102 (accept_3_5 32 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 102
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 30 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 102 (accept_3_5 29 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 102 (Polychromatic418967fa.accept_22_6_15_14_1_4436 28 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 102 (accept_3_5 26 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 37 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 102
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 102 (accept_3_5 23 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 102 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 102 (Polychromatic418967fa.accept_15_6_7_12_1_869 21 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 102 (accept_3_5 20 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 102
  (Polychromatic418967fa.accept_11_7_4_3_1_302 18 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 102 (accept_3_5 17 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 102 (accept_3_5 14 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 102
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 102 (accept_3_5 11 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 102 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 102 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 102 (accept_3_5 8 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 102
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 102 (accept_3_5 5 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  102 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 37 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 102 (accept_3_5 2 37 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 102 (Polychromatic418967fa.accept_16_1_5_6_1_4435 1 37 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 102))))))))))))))))))))))))))))))))))))) (allB_succ 36 102
  (allA_succ_of_accept 35 36 102 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 36 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 102 2 17 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 102 3 11 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 102 2 16 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 31
  36 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 102 6 5 6 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 102
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 29 36 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 102 2 14 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 102 3 9 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 102 2 13 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 102 (Polychromatic418967fa.accept_13_12_10_11_1_1279 25 36 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 102 6 4 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 102 (Polychromatic418967fa.accept_21_2_15_18_1_806 23 36 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 102 2 11 18 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 102 3 7 12 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 102 2 10 18 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 102
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 102 6 3 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 102 2 8 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 102 3 5 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 102 2 7 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 102 (Polychromatic418967fa.accept_16_13_4_6_1_2322 13 36 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 102 6 2 6 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 102
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 36 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 102 2 5 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 36 102 3 3 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 36 102 2 4 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 102 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 36 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 102 6 1 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 102 2 2 18 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 102 3 1 12 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 102 2 1 18 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 102
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 36 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 102)))))))))))))))))))))))))))))))))))) (allB_succ 35 102 (allA_succ_of_accept 34 35 102 (accept_3_4 34
  35 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 102 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 35 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 102 (accept_3_4 31 35 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 102 (Polychromatic418967fa.accept_20_10_15_2_1_3132 30 35 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 102 (accept_3_4 28 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 102 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 102 (Polychromatic418967fa.accept_21_5_14_18_1_4418 26 35 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 102 (accept_3_4 25 35 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 102 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 35 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 102
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 102 (accept_3_4 22 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 35 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 102 (accept_3_4 19 35 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 102 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 102 (accept_3_4 16 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 102 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 102 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 35 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 102 (accept_3_4 13 35 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 102 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 35 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 102
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 102 (accept_3_4 10 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 102 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 35 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 102 (accept_3_4 7 35 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 102 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 35 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 102 (accept_3_4 4 35 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 102 (Polychromatic418967fa.accept_10_3_5_2_1_38 3
  35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 102
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 102 (accept_3_4 1 35 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  102))))))))))))))))))))))))))))))))))) (allB_succ 34 102 (allA_succ_of_accept 33 34 102
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 34 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 102 2 16 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 34 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 102 2 15 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 102 (accept_3_5 29 34 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 102 2 14 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 102 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 34 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 102 2 13 17 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 102
  (Polychromatic418967fa.accept_16_9_2_6_1_4434 25 34 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 102 2 12 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 102 (accept_3_5 23 34 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  102 2 11 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 102 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 34 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 102 2 10 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 34 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 102 2 9 17 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 17 34 102 17 1 2 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 16 34 102 2 8 17 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 102
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 34 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 34 102 2 7 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 34 102 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 34 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 102 2 6 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 102 (accept_3_5 11 34 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 34 102 2 5 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 34 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 34 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 34 102 2 4 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 34 102 (Polychromatic418967fa.accept_10_7_4_2_1_903 7
  34 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 102 2 3 17 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 102 (accept_3_5 5 34
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 102 2 2 17 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 34 102
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 34 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 34 102 2 1 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 34 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 34 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 34 102)))))))))))))))))))))))))))))))))) (allB_succ 33 102
  (allA_succ_of_accept 32 33 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 33 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 102 3 10 11 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 102
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 33 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 33 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 102 3 9 11 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 102 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 33 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 102
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 33 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 33 102 3 8 11 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 33 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 33 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 102 3 7 11 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 102
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 33 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 102 3 6 11 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 102 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 33 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 102
  (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 33 102 3 5 11 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 33 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 33 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 102 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 33 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 102 3 4 11 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 33 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 102 3 3 11 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 33 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 33 102 3 2 11 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 33 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 33 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 33 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 102 3 1 11 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 102
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 33 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 33 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 33 102))))))))))))))))))))))))))))))))) (allB_succ 32 102
  (allA_succ_of_accept 31 32 102 (accept_3_4 31 32 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  102 2 15 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  32 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 32 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 102 2 14 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 32 102 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 32 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 102 2 13 16 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 102 (accept_3_4 25 32 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 102 2 12 16 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 102
  (Polychromatic418967fa.accept_19_4_13_7_1_4433 23 32 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 32 102 2 11 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 32 102 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 32 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 102 2 10 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 102 (accept_3_4 19 32 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 102 2 9 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 32 102 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 32 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 102 2 8 16 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 102
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 32 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 32 102 2 7 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 32 102 (accept_3_4 13 32 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32
  102 2 6 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  32 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 32 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 32 102 2 5 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 32 102 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 32 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 102 2 4 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 102 (accept_3_4 7 32 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 102 2 3 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 32 102 (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 32 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 102 2 2 16 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 102
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 32 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 102 2 1 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 102 (accept_3_4 1 32 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  102)))))))))))))))))))))))))))))))) (allB_succ 31 102 (allA_succ_of_accept 30 31 102
  (Polychromatic418967fa.accept_19_11_12_7_1_3188 30 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 102 (accept_3_5 29 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 102 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 31 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 102 (accept_3_5 26 31 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 102
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 102 (accept_3_5 23 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 102 (accept_3_5 20 31 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 31 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 102
  (Polychromatic418967fa.accept_19_18_12_7_1_4432 18 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 102 (accept_3_5 17 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 31 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 102 (accept_3_5 14 31 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 102
  (Polychromatic418967fa.accept_23_12_8_10_1_4431 12 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 102 (accept_3_5 11 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 102 (accept_3_5 8 31 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 31 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 102
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 102 (accept_3_5 5 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  102 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 31 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 102 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 31 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 102 (accept_3_5 2 31 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 102))))))))))))))))))))))))))))))) (allB_succ 30 102
  (allA_succ_of_accept 29 30 102 (Polychromatic418967fa.accept_21_8_9_18_1_4430 29 30 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 102 2 14 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 102 3 9 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 102 2 13 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 102 (Polychromatic418967fa.accept_13_12_4_11_1_1925
  25 30 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 102 6 4 5 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 102
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 30 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 102 2 11 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 30 102 3 7 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 102 2 10 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 102 6 3 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 102 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 30 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 102 2 8 15 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 102 3 5 10 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 102 2 7 15 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 102
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 30 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 102 6 2 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 102 (Polychromatic418967fa.accept_21_11_9_18_1_4429 11 30 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 102 2 5 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 102 3 3 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 102 2 4 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 102 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 30 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 102 6 1 5 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 102
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 30 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 102 2 2 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 102 3 1 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 102 2 1 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 102 (Polychromatic418967fa.accept_21_1_9_18_1_4428 1 30 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 102)))))))))))))))))))))))))))))) (allB_succ 29 102 (allA_succ_of_accept
  28 29 102 (accept_3_4 28 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 29 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 102 (accept_3_4 25 29 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  29 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 102 (accept_3_4 22 29
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 102
  (Polychromatic418967fa.accept_10_1_9_2_1_45 21 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 102 (Polychromatic418967fa.accept_13_7_3_11_1_280 20 29 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 102 (accept_3_4 19 29 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 102 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 29 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 102
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 102 (accept_3_4 16 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 102 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 29 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 102 (accept_3_4 13 29 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 102
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 102 (accept_3_4 10 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 102 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 102 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 29 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 102 (accept_3_4 7 29 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 102 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 29 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 102
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 102 (accept_3_4 4 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 102 (Polychromatic418967fa.accept_13_2_3_11_1_1287 2 29 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 102 (accept_3_4 1 29 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 102))))))))))))))))))))))))))))) (allB_succ 28 102 (allA_succ_of_accept 27 28 102
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 28 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 102 2 13 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 28 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 102 2 12 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 102 (accept_3_5 23 28 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 102 2 11 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 102 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 28 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 102 2 10 14 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 102
  (Polychromatic418967fa.accept_11_8_6_3_1_661 19 28 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 102 2 9 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 102 (accept_3_5 17 28 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  102 2 8 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 102 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 28 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 102 2 7 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 102 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 28 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 102 2 6 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 102 (accept_3_5 11 28 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 102 2 5 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 28 102 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 28 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 102 2 4 14 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 102
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 28 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 102 2 3 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 102 (accept_3_5 5 28 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 102
  2 2 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28
  102 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 28 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 102 2 1 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 102 (Polychromatic418967fa.accept_15_1_13_12_1_347 1 28 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 102)))))))))))))))))))))))))))) (allB_succ 27 102 (allA_succ_of_accept 26
  27 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 27 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 102 3 8 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 23
  27 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 102
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 27 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 102 3 7 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 102 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 27 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 102 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 27 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 102 3 6 9 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 27 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 102 3 5 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 102 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 27 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 102 3 4 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 102 (Polychromatic418967fa.accept_18_11_9_12_1_4427 11 27 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 27 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 102 3 3 9 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 102
  (Polychromatic418967fa.accept_11_8_5_3_1_694 8 27 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 102 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 27 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 102 3 2 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 102
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 27 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 102 3 1 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 27 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 102))))))))))))))))))))))))))) (allB_succ 26
  102 (allA_succ_of_accept 25 26 102 (accept_3_4 25 26 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  26 102 2 12 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 26 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 102 2 11 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 102 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 26 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 102 2 10 13 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 102 (accept_3_4 19 26 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 102 2 9 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 102 (Polychromatic418967fa.accept_23_17_3_10_1_4426
  17 26 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 102 2 8 13 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 102
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 26 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 102 2 7 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 102 (accept_3_4 13 26 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  102 2 6 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 26 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 102 2 5 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 26 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 102 2 4 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 102 (accept_3_4 7 26 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 102 2 3 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 102 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 26 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 102 2 2 13 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 102
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 26 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 102 2 1 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 102 (accept_3_4 1 26 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  102)))))))))))))))))))))))))) (allB_succ 25 102 (allA_succ_of_accept 24 25 102
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 102 (accept_3_5 23 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 102 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 102 (Polychromatic418967fa.accept_14_7_11_4_1_3455 21 25 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 102 (accept_3_5 20 25 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 102
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 102 (accept_3_5 17 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 102 (Polychromatic418967fa.accept_19_16_6_7_1_4425 16 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 102 (accept_3_5 14 25 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 102 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 25 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 102
  (Polychromatic418967fa.accept_21_12_4_18_1_4424 12 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 102 (accept_3_5 11 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 102 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 25 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 102 (accept_3_5 8 25 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 102
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 102 (accept_3_5 5 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  102 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 25 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 102 (accept_3_5 2 25 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 25 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 102))))))))))))))))))))))))) (allB_succ 24 102
  (allA_succ_of_accept 23 24 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 24 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 102 2 11 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 102 3 7 8 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 102 2 10 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 19
  24 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 102 6 3 4 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 102
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 24 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 102 2 8 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 102 3 5 8 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 102 2 7 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 102 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 102 6 2 4 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 102 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 24 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 102 2 5 12 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 102 3 3 8 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 102 2 4 12 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 102
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 24 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 102 6 1 4 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 102 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 24 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 102 2 2 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 102 3 1 8 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 102 2 1 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 102)))))))))))))))))))))))) (allB_succ 23
  102 (allA_succ_of_accept 22 23 102 (accept_3_4 22 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 23 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 102 (accept_3_4 19 23 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 102 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 23 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 102 (accept_3_4 16 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 102 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 102 (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 23 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 102 (accept_3_4 13 23 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 102
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 102 (accept_3_4 10 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 102 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 23 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 102 (accept_3_4 7 23 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 23 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 102 (accept_3_4 4 23 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 102 (Polychromatic418967fa.accept_13_3_10_11_1_1293
  3 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 102
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 102 (accept_3_4 1 23 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  102))))))))))))))))))))))) (allB_succ 22 102 (allA_succ_of_accept 21 22 102
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 22 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 102 2 10 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 102 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 22 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 102 2 9 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 102 (accept_3_5 17 22 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 102 2 8 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 102 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 22 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 102 2 7 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 102 (Polychromatic418967fa.accept_19_13_3_7_1_4423
  13 22 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 102 2 6 11 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 102 (accept_3_5 11
  22 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 102 2 5 11 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 102
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 22 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 102 2 4 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 102 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 22 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 102 2 3 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 102 (accept_3_5 5 22 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 102 2 2 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 22 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 102 2 1 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 22
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 102)))))))))))))))))))))) (allB_succ 21
  102 (allA_succ_of_accept 20 21 102 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 21 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 102 3 6 7 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 102
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 17 21 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 102 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 21 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 102 3 5 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 102 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 21 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 102
  (Polychromatic418967fa.accept_10_3_1_2_1_521 13 21 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 102 3 4 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 102 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 21
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 102 3 3 7 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 102
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 21 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 102 3 2 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 102 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 21 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 102
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 21 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 102 3 1 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 102 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 21 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 102 (Polychromatic418967fa.accept_13_1_8_11_1_724 1 21 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 102))))))))))))))))))))) (allB_succ 20 102
  (allA_succ_of_accept 19 20 102 (accept_3_4 19 20 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20
  102 2 9 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  20 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 20 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 20 102 2 8 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 20 102 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 20 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 102 2 7 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 102 (accept_3_4 13 20 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 102 2 6 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 20 102 (Polychromatic418967fa.accept_16_11_4_6_1_4422 11 20 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 102 2 5 10 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 102
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 20 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 102 2 4 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 102 (accept_3_4 7 20 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 102
  2 3 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  102 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 20 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 102 2 2 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 20 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 102 2 1 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 102 (accept_3_4 1 20 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 102)))))))))))))))))))) (allB_succ 19 102 (allA_succ_of_accept 18 19 102
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 19 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 102 (accept_3_5 17 19 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 102 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 19 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 19 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 102 (accept_3_5 14 19 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 102
  (Polychromatic418967fa.accept_20_12_19_2_1_4421 12 19 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 102 (accept_3_5 11 19 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 102 (Polychromatic418967fa.accept_25_10_19_2_1_4420 10 19 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 102 (accept_3_5 8 19 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 102 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 19 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 102
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 102 (accept_3_5 5 19 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  102 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 19 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 102 (Polychromatic418967fa.accept_18_3_1_12_1_4419 3 19 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 102 (accept_3_5 2 19 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 102))))))))))))))))))) (allB_succ 18 102 (allA_succ_of_accept 17
  18 102 (Polychromatic418967fa.accept_15_2_3_12_1_891 17 18 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 18 102 2 8 9 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 18 102 3 5 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 18 102 2 7 9 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 102 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 18 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 102 6 2 3 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 102
  (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 18 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 18 102 2 5 9 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 18 102 3 3 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 18 102 2 4 9 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 18 102 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 18 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 102 6 1 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 102 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 18 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 102 2 2 9 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 102 3 1 6 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 102 2 1 9 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 102
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 1 18 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 102)))))))))))))))))) (allB_succ 17 102 (allA_succ_of_accept 16 17 102 (accept_3_4 16 17 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 102
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 17 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 102 (accept_3_4 13 17 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 102 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 17 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 102 (accept_3_4 10 17 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 102 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 17 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 102
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 17 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 102 (accept_3_4 7 17 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  102 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 17 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 102 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 17 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 102 (accept_3_4 4 17 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 102 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  17 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 102 (accept_3_4 1 17 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 102))))))))))))))))) (allB_succ 16 102 (allA_succ_of_accept 15
  16 102 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 16 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 16 102 2 7 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 16 102 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 16 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 102 2 6 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 102 (accept_3_5 11 16 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16 102 2 5 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 16 102 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 16 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 102 2 4 8 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 102
  (Polychromatic418967fa.accept_13_7_3_11_1_280 7 16 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 16 102 2 3 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 16 102 (accept_3_5 5 16 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 102
  2 2 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 102
  (Polychromatic418967fa.accept_12_3_4_6_1_434 3 16 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 102 2 1 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 102 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 16 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 102)))))))))))))))) (allB_succ 15 102 (allA_succ_of_accept 14 15 102
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 15 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 102 3 4 5 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 102 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 15 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 102
  (Polychromatic418967fa.accept_7_3_1_4_1_121 10 15 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 102 3 3 5 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 102 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 15 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 102 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 15 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 102 3 2 5 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 102 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 15 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 102 3 1 5 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 102 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 15 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 102))))))))))))))) (allB_succ 14 102 (allA_succ_of_accept 13 14 102 (accept_3_4 13 14 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 102 2 6 7 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 102 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 14 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 102 2 5 7 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 102
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 14 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 102 2 4 7 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 102 (accept_3_4 7 14 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 102
  2 3 7 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 102
  (Polychromatic418967fa.accept_21_5_14_18_1_4418 5 14 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 102 2 2 7 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 102 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 14 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 102 2 1 7 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 102 (accept_3_4 1 14 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 102)))))))))))))) (allB_succ 13 102 (allA_succ_of_accept 12 13 102
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 102 (accept_3_5 11 13 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 102 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 13 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 102 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 13 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 102 (accept_3_5 8 13 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 102
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 13 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 102 (accept_3_5 5 13 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  102 (Polychromatic418967fa.accept_16_4_13_6_1_4417 4 13 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 102 (accept_3_5 2 13 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 13 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 102))))))))))))) (allB_succ 12 102
  (allA_succ_of_accept 11 12 102 (Polychromatic418967fa.accept_19_11_12_7_1_3188 11 12 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 102 2 5 6 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 12 102 3 3 4 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 12 102 2 4 6 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 102 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 12 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 102 6 1 2 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 102
  (Polychromatic418967fa.accept_19_5_12_7_1_4416 5 12 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 102 2 2 6 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 12 102 3 1 4 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 12 102 2 1 6 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 102 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 102)))))))))))) (allB_succ 11 102 (allA_succ_of_accept 10 11 102
  (accept_3_4 10 11 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 102
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 102 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 11 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 102 (accept_3_4 7 11 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 102 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 11 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 102 (accept_3_4 4 11 102
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 102 (Polychromatic418967fa.accept_10_3_1_2_1_521 3
  11 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 102
  (Polychromatic418967fa.accept_16_2_11_6_1_737 2 11 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 102 (accept_3_4 1 11 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  102))))))))))) (allB_succ 10 102 (allA_succ_of_accept 9 10 102 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 10 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 102 2 4 5 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 102
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 10 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 102 2 3 5 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 102 (accept_3_5 5 10 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 102
  2 2 5 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 102
  (Polychromatic418967fa.accept_12_3_10_6_1_442 3 10 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 102 2 1 5 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 102 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 10 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 102)))))))))) (allB_succ 9 102 (allA_succ_of_accept 8 9 102
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 9 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 102 3 2 3 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 102 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 102
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 9 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 102 3 1 3 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 102 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 9 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 102 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 9 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 102))))))))) (allB_succ 8 102
  (allA_succ_of_accept 7 8 102 (accept_3_4 7 8 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 102 2
  3 4 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 102
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 8 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 102 2 2 4 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 102 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 8 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 102 2 1 4 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 102 (accept_3_4 1 8 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 102)))))))) (allB_succ 7 102 (allA_succ_of_accept 6 7 102
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 7 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 102 (accept_3_5 5 7 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 102
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 7 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 102 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 7 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 102 (accept_3_5 2 7 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 102))))))) (allB_succ 6 102 (allA_succ_of_accept 5 6 102
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 6 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 102 2 2 3 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 102 3 1 2 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 102 2 1 3 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 102 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 6 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 102)))))) (allB_succ 5 102 (allA_succ_of_accept 4 5 102 (accept_3_4 4 5
  102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 102 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  5 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 102
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 5 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 102 (accept_3_4 1 5 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 102)))))
  (allB_succ 4 102 (allA_succ_of_accept 3 4 102 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 4 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 102 2 1 2 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 102 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 4
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 102)))) (allB_succ 3 102
  (allA_succ_of_accept 2 3 102 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 3 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 102 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 102))) (allB_succ 2 102 (allA_succ_of_accept
  1 2 102 (accept_3_4 1 2 102 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 102)) (allB_two
  102))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


