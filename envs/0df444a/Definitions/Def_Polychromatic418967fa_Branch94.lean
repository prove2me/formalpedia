-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch94
-- name    : Polychromatic418967fa_Branch94
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:16.131935+00:00
-- url     : https://prove2.me/theorems/5cadbb98-8a36-4f8b-ba9e-db9b940bb3ab
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

def Polychromatic418967fa.branch_94 : allB 94 94 :=
  allB_succ' 2 93 94 (Eq.refl Bool.true) (allA_succ_of_accept 1 93 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 94)) (allB_succ' 3 92 94 (Eq.refl Bool.true)
  (allA_of_3_1 3 92 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 91 94 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 91 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 94 (accept_3_3 2 91 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 94)))) (allB_succ' 5 90 94 (Eq.refl Bool.true) (allA_succ_of_gcd
  4 90 94 2 2 45 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 90 94 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 90 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 90 94 2 1 45 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 90 94 (Polychromatic418967fa.accept_19_1_14_18_1_3919 1 90 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 94))))) (allB_succ' 6 89 94 (Eq.refl Bool.true) (allA_of_3_1 6
  89 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 88 94 (Eq.refl Bool.true) (allA_succ_of_gcd 6 88 94 2 3
  44 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 94
  (accept_3_3 5 88 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 94 2 2 44 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88 94
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 88 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 94 2 1 44 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 94 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 88 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88 94))))))) (allB_succ' 8 87 94 (Eq.refl Bool.true) (allA_succ_of_accept 7
  87 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 94 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 87 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 94 (accept_3_3 5 87 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 94 (Polychromatic418967fa.accept_16_4_7_14_1_3897 4 87 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 87
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 94 (accept_3_3 2 87 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 94)))))))) (allB_succ' 9 86 94 (Eq.refl
  Bool.true) (allA_of_3_1 9 86 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 85 94 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 85 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 94 (accept_3_3 8 85 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 85 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 94 (Polychromatic418967fa.accept_10_6_5_4_1_571 6
  85 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 94 (accept_3_3 5 85 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 94 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 85
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 94 (accept_3_3 2 85 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 94
  (Polychromatic418967fa.accept_10_1_5_4_1_276 1 85 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 85 94)))))))))) (allB_succ' 11 84 94 (Eq.refl Bool.true) (allA_succ_of_gcd 10 84 94 2 5 42 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 94
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 84 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 94 2 4 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 94 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 94 2 3 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 94 (accept_3_3 5 84 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 84 94 2 2 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 84 94 (Polychromatic418967fa.accept_20_3_4_14_1_3918 3 84 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 94 2 1 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 94 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 94))))))))))) (allB_succ' 12 83 94
  (Eq.refl Bool.true) (allA_of_3_1 12 83 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 82 94 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 82 94 2 6 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 82 94 (accept_3_3 11 82 94 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 82 94 2 5 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 82 94 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 82 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 82 94 2 4 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 82 94 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 94 2 3 41 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 94 (accept_3_3 5 82 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 94 2 2 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82 94 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 82 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 94 2 1 41 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 94
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 82 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 94))))))))))))) (allB_succ' 14 81 94 (Eq.refl Bool.true) (allA_succ_of_accept 13 81 94
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 81 94 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 81 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 94 (accept_3_3 11 81 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 81 94 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 81 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 94 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9
  81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 94 (accept_3_3 8 81 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 94
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 94 (accept_3_3 5 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 94
  (Polychromatic418967fa.accept_16_4_1_14_1_3908 4 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 81 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 94 (accept_3_3 2 81 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 81 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 94)))))))))))))) (allB_succ' 15 80 94 (Eq.refl Bool.true)
  (allA_of_3_1 15 80 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 79 94 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 79 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 94 (accept_3_3 14 79 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 79 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 94 (Polychromatic418967fa.accept_7_5_2_3_1_106 12
  79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 94 (accept_3_3 11 79 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 10
  79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 94 (accept_3_3 8 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 94
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 79 94 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 94 (accept_3_3 5 79 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 79 94 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 79 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 94 (accept_3_3 2 79 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 94)))))))))))))))) (allB_succ' 17 78 94
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 78 94 2 8 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 78 94 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 78 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 94 2 7 39 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 94
  (Polychromatic418967fa.accept_17_13_10_9_1_946 13 78 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 94 2 6 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 94 (accept_3_3 11 78 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 94
  2 5 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 94
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 94 2 4 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 94 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 94 2 3 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 94 (accept_3_3 5 78 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 94 2 2 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 78 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 94 2 1 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 94))))))))))))))))) (allB_succ' 18 77 94
  (Eq.refl Bool.true) (allA_of_3_1 18 77 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 76 94 (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 76 94 2 9 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 76 94 (accept_3_3 17 76 94 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 76 94 2 8 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 76 94 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 76 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 94 2 7 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 94 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 76 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 94 2 6 38 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 94 (accept_3_3 11 76 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 94 2 5 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 94 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 76
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 94 2 4 38 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 94
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 76 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 94 2 3 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 94 (accept_3_3 5 76 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 94 2
  2 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76 94
  (Polychromatic418967fa.accept_14_3_6_10_1_752 3 76 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 94 2 1 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 94 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 76 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76 94))))))))))))))))))) (allB_succ' 20 75 94 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 75 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 94 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 75 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 94 (accept_3_3 17 75 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 94 (Polychromatic418967fa.accept_7_2_5_3_1_98 16
  75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 94
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 94 (accept_3_3 14 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75
  94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 94 (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 75 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 94 (accept_3_3 11 75 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 75 94 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 75 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 94 (accept_3_3 8 75 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 94
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 94 (accept_3_3 5 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 94
  (Polychromatic418967fa.accept_22_4_9_6_1_3917 4 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 94 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 75 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 94 (accept_3_3 2 75 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 94)))))))))))))))))))) (allB_succ' 21 74 94 (Eq.refl Bool.true)
  (allA_of_3_1 21 74 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 73 94 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 73 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 94 (accept_3_3 20 73 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 73 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 94 (Polychromatic418967fa.accept_13_5_8_3_1_1535
  18 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 94 (accept_3_3 17 73
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 94 (Polychromatic418967fa.accept_9_7_1_4_1_217
  16 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 94 (accept_3_3 14 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 73
  94 (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 94 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 73 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 94 (accept_3_3 11 73 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 94 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 73 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 94 (accept_3_3 8 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 94 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 73 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 94 (accept_3_3 5 73 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 94 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 73 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 94 (accept_3_3 2 73 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 94 (Polychromatic418967fa.accept_11_1_7_6_1_378 1
  73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 94)))))))))))))))))))))) (allB_succ'
  23 72 94 (Eq.refl Bool.true) (allA_succ_of_gcd 22 72 94 2 11 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 94 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 72 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 94 2 10 36 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 94
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 94 2 9 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 94 (accept_3_3 17 72 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 94
  2 8 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72
  94 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 72 94 2 7 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 94 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 94 2 6 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 94 (accept_3_3 11 72 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 72 94 2 5 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 72 94 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 72 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 94 2 4 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 94 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 72
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 94 2 3 36 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 94 (accept_3_3 5 72
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 94 2 2 36 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 94
  (Polychromatic418967fa.accept_19_3_15_18_1_2682 3 72 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 72 94 2 1 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 94 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72 94))))))))))))))))))))))) (allB_succ' 24 71 94 (Eq.refl Bool.true)
  (allA_of_3_1 24 71 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 70 94 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 70 94 2 12 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 70 94 (accept_3_3 23 70 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 94
  2 11 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70
  94 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 70 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 94 2 10 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 94 2 9 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 94 (accept_3_3 17 70 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 70 94 2 8 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 70 94 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 70 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 94 2 7 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 94 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13
  70 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 94 2 6 35 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 94 (accept_3_3 11 70
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 94 2 5 35 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 94
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 70 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 94 2 4 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 94 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 70 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 94 2 3 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 94 (accept_3_3 5 70 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 94 2 2 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 94 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 70 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 94 2 1 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 94))))))))))))))))))))))))) (allB_succ'
  26 69 94 (Eq.refl Bool.true) (allA_succ_of_accept 25 69 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 94
  (Polychromatic418967fa.accept_18_6_15_4_1_3916 24 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 94 (accept_3_3 23 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69
  94 (Polychromatic418967fa.accept_32_22_5_30_1_3915 22 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 94 (accept_3_3 20 69 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 94
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 94 (accept_3_3 17 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69
  94 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 69 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 94 (accept_3_3 14 69 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 69 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 12
  69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 94 (accept_3_3 11 69 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 10
  69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 94
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 94 (accept_3_3 8 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 94 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 69 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 94 (accept_3_3 5 69 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 94 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 69 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 94 (accept_3_3 2 69 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 94)))))))))))))))))))))))))) (allB_succ'
  27 68 94 (Eq.refl Bool.true) (allA_of_3_1 27 68 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 67 94
  (Eq.refl Bool.true) (allA_succ_of_accept 27 67 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 94 (accept_3_3 26 67 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 94
  (Polychromatic418967fa.accept_13_11_2_3_1_883 24 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 94 (accept_3_3 23 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 67
  94 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 67 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 94 (accept_3_3 20 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 67 94 (Polychromatic418967fa.accept_21_19_4_10_1_3914 19 67 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 94 (Polychromatic418967fa.accept_11_7_1_6_1_1281
  18 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 94 (accept_3_3 17 67
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 94 (Polychromatic418967fa.accept_11_5_1_6_1_774
  16 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 94 (accept_3_3 14 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67
  94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 67 94 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 94 (accept_3_3 11 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 67 94 (Polychromatic418967fa.accept_13_10_2_3_1_3025 10 67 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 94 (accept_3_3 8 67 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 94 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7
  67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 94
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 94 (accept_3_3 5 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 94
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 67 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 94 (accept_3_3 2 67 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 94)))))))))))))))))))))))))))) (allB_succ' 29 66 94 (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 66 94 2 14 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 66 94 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 66 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 94 2 13 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 94 (Polychromatic418967fa.accept_9_7_3_4_1_218 25
  66 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 94 2 12 33 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 94 (accept_3_3 23 66
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 94 2 11 33 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 94
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 94 2 10 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 94 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 66 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 94 2 9 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 94 (accept_3_3 17 66 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 94 2 8 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 94 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 66 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 94 2 7 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 94 (Polychromatic418967fa.accept_15_13_6_4_1_1221
  13 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 94 2 6 33 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 94 (accept_3_3 11 66
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 94 2 5 33 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 94
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 66 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 94 2 4 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 94 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 94 2 3 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 94 (accept_3_3 5 66 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 94 2 2 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 94 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 66 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 94 2 1 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 94 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 66
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 94)))))))))))))))))))))))))))))
  (allB_succ' 30 65 94 (Eq.refl Bool.true) (allA_of_3_1 30 65 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31
  64 94 (Eq.refl Bool.true) (allA_succ_of_gcd 30 64 94 2 15 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 94 (accept_3_3 29 64 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 64 94 2 14 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 64 94 (Polychromatic418967fa.accept_17_10_13_9_1_3913 27 64 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 94 2 13 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 94 (Polychromatic418967fa.accept_7_4_1_3_1_277 25
  64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 94 2 12 32 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 94 (accept_3_3 23 64
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 94 2 11 32 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 94
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 64 94 2 10 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 64 94 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 64 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 94 2 9 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 94 (accept_3_3 17 64 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 64 94 2 8 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 64 94 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 64 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 94 2 7 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 94 (Polychromatic418967fa.accept_12_1_4_10_1_209 13
  64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 94 2 6 32 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 94 (accept_3_3 11 64
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 94 2 5 32 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 94
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 94 2 4 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 94 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 94 2 3 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 94 (accept_3_3 5 64 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 94 2 2 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 94 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 64 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 94 2 1 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 94 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  64 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 94)))))))))))))))))))))))))))))))
  (allB_succ' 32 63 94 (Eq.refl Bool.true) (allA_succ_of_accept 31 63 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 94
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 94 (accept_3_3 29 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63
  94 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 63 94 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 63 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 94 (accept_3_3 26 63 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 63 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 94 (Polychromatic418967fa.accept_19_5_6_18_1_3912
  24 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 94 (accept_3_3 23 63
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 94 (Polychromatic418967fa.accept_15_7_3_4_1_574
  22 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 94 (accept_3_3 20 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63
  94 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 94 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 63 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 94 (accept_3_3 17 63 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 63 94 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 63 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 94 (Polychromatic418967fa.accept_13_2_11_3_1_873
  15 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 94 (accept_3_3 14 63
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 94
  (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 94 (accept_3_3 11 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63
  94 (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 94 (accept_3_3 8 63 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 63 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 94 (Polychromatic418967fa.accept_12_6_3_10_1_224 6
  63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 94 (accept_3_3 5 63 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 94 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4
  63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 94
  (Polychromatic418967fa.accept_11_3_8_6_1_788 3 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 94 (accept_3_3 2 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 94)))))))))))))))))))))))))))))))) (allB_succ' 33 62 94 (Eq.refl Bool.true) (allA_of_3_1 33 62 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 61 94 (Eq.refl Bool.true) (allA_succ_of_accept 33 61 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 61 94 (accept_3_3 32 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61
  94 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 61 94 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 94 (accept_3_3 29 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 61 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 94 (accept_3_3 26 61 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 94 (Polychromatic418967fa.accept_10_5_1_4_1_1444
  25 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 94
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 94 (accept_3_3 23 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 61
  94 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 61 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 94 (accept_3_3 20 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 61 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 94 (Polychromatic418967fa.accept_13_5_9_3_1_870 18
  61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 94 (accept_3_3 17 61 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 94 (Polychromatic418967fa.accept_7_2_5_3_1_98 16
  61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 94 (accept_3_3 14 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61
  94 (Polychromatic418967fa.accept_17_13_10_9_1_946 13 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 61 94 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 94 (accept_3_3 11 61 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 61 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 61 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 94 (accept_3_3 8 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 61 94 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 94 (accept_3_3 5 61 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 61 94 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 61 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 94 (accept_3_3 2 61 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 94 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 94))))))))))))))))))))))))))))))))))
  (allB_succ' 35 60 94 (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 94 2 17 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 94 (Polychromatic418967fa.accept_13_7_8_3_1_1533 33
  60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 94 2 16 30 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 94
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 31 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 94 2 15 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 94 (accept_3_3 29 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 94
  2 14 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60
  94 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 60 94 2 13 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 60 94 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 94 2 12 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 94 (accept_3_3 23 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 60 94 2 11 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 60 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 94 2 10 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 60
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 94 2 9 30 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 94 (accept_3_3 17 60
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 94 2 8 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 94
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 60 94 2 7 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 94 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 94 2 6 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 94 (accept_3_3 11 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 94 2 5 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 60 94 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 60 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 94 2 4 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 94 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 94 2 3 30 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 94 (accept_3_3 5 60
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 94 2 2 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 94
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 60 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 94 2 1 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 94 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 94))))))))))))))))))))))))))))))))))) (allB_succ' 36 59 94 (Eq.refl
  Bool.true) (allA_of_3_1 36 59 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 58 94 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 58 94 2 18 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 58 94 (accept_3_3 35 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 94
  2 17 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58
  94 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 58 94 2 16 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 58 94 (Polychromatic418967fa.accept_11_9_3_6_1_797 31 58 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 94 2 15 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 94 (accept_3_3 29 58 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 58 94 2 14 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 58 94 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 58 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 94 2 13 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 94 (Polychromatic418967fa.accept_15_10_13_4_1_1210
  25 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 94 2 12 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 94 (accept_3_3 23 58
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 94 2 11 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 94
  (Polychromatic418967fa.accept_15_6_13_4_1_2040 21 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 94 2 10 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 94 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 58 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 94 2 9 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 94 (accept_3_3 17 58 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 94 2 8 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 94 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 58 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 94 2 7 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 94 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 94 2 6 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 94 (accept_3_3 11 58
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 94 2 5 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 94
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 58 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 94 2 4 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 94 (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 58 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 94 2 3 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 94 (accept_3_3 5 58 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 94 2 2 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 94 (Polychromatic418967fa.accept_21_3_16_10_1_3911 3 58 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 94 2 1 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 94 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 58
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 94)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 57 94 (Eq.refl Bool.true) (allA_succ_of_accept 37 57 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 94
  (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 94 (accept_3_3 35 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57
  94 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 57 94 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 94 (accept_3_3 32 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 57 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 94 (Polychromatic418967fa.accept_7_2_1_3_1_102 30
  57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 94 (accept_3_3 29 57 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 94 (Polychromatic418967fa.accept_9_1_3_4_1_47 28
  57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 94 (accept_3_3 26 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57
  94 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 94 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 94 (accept_3_3 23 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 94 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 57 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 94 (Polychromatic418967fa.accept_10_1_7_4_1_968 21
  57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 94 (accept_3_3 20 57 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 94
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 94 (accept_3_3 17 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57
  94 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 57 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 94 (accept_3_3 14 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 57 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 94 (Polychromatic418967fa.accept_7_5_1_3_1_103 12
  57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 94 (accept_3_3 11 57 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 94 (Polychromatic418967fa.accept_9_1_3_4_1_47 10
  57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 94
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 94 (accept_3_3 8 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 94 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 94 (accept_3_3 5 57 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 94 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 94 (accept_3_3 2 57 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 94))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 56 94 (Eq.refl Bool.true) (allA_of_3_1 39 56 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40
  55 94 (Eq.refl Bool.true) (allA_succ_of_accept 39 55 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 94 (accept_3_3 38 55 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 94
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 94 (accept_3_3 35 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55
  94 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 94 (accept_3_3 32 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 94 (Polychromatic418967fa.accept_10_1_5_4_1_276 31 55 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 94 (Polychromatic418967fa.accept_7_2_6_3_1_100 30
  55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 94 (accept_3_3 29 55 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 94 (Polychromatic418967fa.accept_12_4_7_10_1_563
  28 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 94 (accept_3_3 26 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55
  94 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 55 94 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 94 (accept_3_3 23 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 55 94 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 55 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 94 (accept_3_3 20 55 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 94 (Polychromatic418967fa.accept_10_9_5_4_1_966 19
  55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 94
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 94 (accept_3_3 17 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55
  94 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 55 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 94 (accept_3_3 14 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 55 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 94 (Polychromatic418967fa.accept_9_3_1_4_1_216 12
  55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 94 (accept_3_3 11 55 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 94 (Polychromatic418967fa.accept_16_10_7_14_1_2882
  10 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 94 (accept_3_3 8 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 94
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 94 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 94 (accept_3_3 5 55 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 94 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 94 (accept_3_3 2 55 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  94)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 54 94 (Eq.refl Bool.true) (allA_succ_of_gcd 40 54 94 2 20 27
  47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 94
  (Polychromatic418967fa.accept_12_3_6_10_1_576 39 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 94 2 19 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 54 94 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 94 2 18 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 94 (accept_3_3 35 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 54 94 2 17 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 54 94 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 94 2 16 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 94 (Polychromatic418967fa.accept_13_5_2_3_1_1526 31
  54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 94 2 15 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 94 (accept_3_3 29 54
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 94 2 14 27 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 94
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 94 2 13 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 94 (Polychromatic418967fa.accept_13_12_2_3_1_1527 25 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 94 2 12 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 94 (accept_3_3 23 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 94 2 11 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 54 94 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 94 2 10 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 94 (Polychromatic418967fa.accept_14_5_12_10_1_2985
  19 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 94 2 9 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 94 (accept_3_3 17 54
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 94 2 8 27 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 94
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 94 2 7 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 94 (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 94 2 6 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 94 (accept_3_3 11 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 94 2 5 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 94 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 94 2 4 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 94 (Polychromatic418967fa.accept_33_7_21_28_1_3910 7
  54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 94 2 3 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 94 (accept_3_3 5 54
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 94 2 2 27 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 94
  (Polychromatic418967fa.accept_12_3_6_10_1_576 3 54 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 94 2 1 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 94 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 54 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 94))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 53 94 (Eq.refl
  Bool.true) (allA_of_3_1 42 53 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 52 94 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 52 94 2 21 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 94 (accept_3_3 41 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 94
  2 20 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52
  94 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 52 94 2 19 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 52 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 94 2 18 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 94 (accept_3_3 35 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 52 94 2 17 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 52 94 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 52 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 94 2 16 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 94 (Polychromatic418967fa.accept_12_7_4_10_1_572 31
  52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 94 2 15 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 94 (accept_3_3 29 52
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 94 2 14 26 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 94
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 94 2 13 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 94 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 94 2 12 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 94 (accept_3_3 23 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 52 94 2 11 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 52 94 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 52 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 94 2 10 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 94 2 9 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 94 (accept_3_3 17 52
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 94 2 8 26 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 94
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 52 94 2 7 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 52 94 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 94 2 6 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 94 (accept_3_3 11 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 52 94 2 5 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 52 94 (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 52 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 94 2 4 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 94 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 52
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 94 2 3 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 94 (accept_3_3 5 52
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 94 2 2 26 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52 94
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 52 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 94 2 1 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 52 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 94))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 51 94
  (Eq.refl Bool.true) (allA_succ_of_accept 43 51 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 94
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 94 (accept_3_3 41 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51
  94 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 51 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 94 (accept_3_3 38 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 51 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 94 (Polychromatic418967fa.accept_7_1_2_3_1_257 36
  51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 94 (accept_3_3 35 51 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 94 (Polychromatic418967fa.accept_7_6_2_3_1_107 34
  51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 94 (accept_3_3 32 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51
  94 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 51 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 94 (accept_3_3 29 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 51 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 51 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 94 (Polychromatic418967fa.accept_7_6_2_3_1_107 27
  51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 94 (accept_3_3 26 51 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 94
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 94 (accept_3_3 23 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51
  94 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 51 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 94 (accept_3_3 20 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 51 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 94 (Polychromatic418967fa.accept_12_6_3_10_1_224
  18 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 94 (accept_3_3 17 51
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 94 (Polychromatic418967fa.accept_9_7_6_4_1_483
  16 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 94
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 94 (accept_3_3 14 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51
  94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 51 94 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 94 (accept_3_3 11 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 51 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 94 (accept_3_3 8 51 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 94
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 94 (accept_3_3 5 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 94
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 51 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 94 (accept_3_3 2 51 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 94)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 50
  94 (Eq.refl Bool.true) (allA_of_3_1 45 50 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 49 94 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 49 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 94 (accept_3_3 44 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 49 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 94
  (Polychromatic418967fa.accept_19_4_11_18_1_3909 42 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 94 (accept_3_3 41 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49
  94 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 49 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 94 (accept_3_3 38 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 49 94 (Polychromatic418967fa.accept_13_11_10_3_1_3020 37 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 94 (Polychromatic418967fa.accept_16_4_1_14_1_3908
  36 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 94 (accept_3_3 35 49
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 94 (Polychromatic418967fa.accept_11_1_5_6_1_397
  34 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 94 (accept_3_3 32 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49
  94 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 49 94 (Polychromatic418967fa.accept_21_9_7_10_1_3907 30 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 94 (accept_3_3 29 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 49 94 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 94 (accept_3_3 26 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 94 (Polychromatic418967fa.accept_10_5_9_4_1_1420
  25 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 94
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 94 (accept_3_3 23 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49
  94 (Polychromatic418967fa.accept_19_3_11_18_1_2709 22 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 94 (accept_3_3 20 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 94
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 94 (accept_3_3 17 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49
  94 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 49 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 94 (accept_3_3 14 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 49 94 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 94 (Polychromatic418967fa.accept_11_1_5_6_1_397 12
  49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 94 (accept_3_3 11 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 94 (Polychromatic418967fa.accept_11_10_5_6_1_1842
  10 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 94 (accept_3_3 8 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 94 (Polychromatic418967fa.accept_13_6_10_3_1_897 6 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 94 (accept_3_3 5 49 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 94 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 49 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 94 (accept_3_3 2 49 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 94 (Polychromatic418967fa.accept_11_1_5_6_1_397 1
  49 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  94)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 48 94 (Eq.refl Bool.true) (allA_succ_of_gcd 46 48 94 2
  23 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 94
  (Polychromatic418967fa.accept_13_6_9_3_1_915 45 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 94 2 22 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 94 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 48 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 94 2 21 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 94 (accept_3_3 41 48 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 94 2 20 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 48 94 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 94 2 19 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 94 (Polychromatic418967fa.accept_7_2_6_3_1_100 37
  48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 94 2 18 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 94 (accept_3_3 35 48
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 94 2 17 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 94
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 94 2 16 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 94 (Polychromatic418967fa.accept_13_5_9_3_1_870 31 48 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 94 2 15 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 94 (accept_3_3 29 48 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 94 2 14 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 94 (Polychromatic418967fa.accept_18_9_12_4_1_1659 27 48 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 94 2 13 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 94 (Polychromatic418967fa.accept_7_4_6_3_1_271 25
  48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 94 2 12 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 94 (accept_3_3 23 48
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 94 2 11 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 94
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 94 2 10 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 94 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 94 2 9 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 94 (accept_3_3 17 48 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 94 2 8 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 94 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 94 2 7 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 94 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13
  48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 94 2 6 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 94 (accept_3_3 11 48
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 94 2 5 24 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 94
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 94 2 4 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 94 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 94 2 3 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 94 (accept_3_3 5 48 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 94 2 2 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 94 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 48 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 94 2 1 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 94 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  94))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 94 (allA_of_3_1 47 47 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 46 94 (allA_succ_of_accept 45 46 94 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 46 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 46 94 2 22 23 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 46 94
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 46 94 2 21 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 46 94 (accept_3_3 41 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 94
  2 20 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46
  94 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 94 2 19 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 46 94 (Polychromatic418967fa.accept_11_4_2_6_1_389 37 46 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 94 2 18 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 94 (accept_3_3 35 46 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 46 94 2 17 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 46 94 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 46 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 94 2 16 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 94 (Polychromatic418967fa.accept_17_14_12_9_1_2774
  31 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 94 2 15 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 94 (accept_3_3 29 46
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 94 2 14 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 94
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 94 2 13 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 94 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 94 2 12 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 94 (accept_3_3 23 46 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 46 94 2 11 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 46 94 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 46 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 94 2 10 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 94 (Polychromatic418967fa.accept_20_19_6_14_1_3906
  19 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 94 2 9 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 94 (accept_3_3 17 46
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46 94 2 8 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 46 94
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 46 94 2 7 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 46 94 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 46 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 94 2 6 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 94 (accept_3_3 11 46 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 46 94 2 5 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 46 94 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 46 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 94 2 4 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 94 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 94 2 3 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 94 (accept_3_3 5 46
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 94 2 2 23 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46 94
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 46 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 94 2 1 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 94 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 46 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 94)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 94
  (allA_succ_of_accept 44 45 94 (accept_3_3 44 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45
  94 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 94 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 94 (accept_3_3 41 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 94 (Polychromatic418967fa.accept_11_7_1_6_1_1281 40 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 94 (accept_3_3 38 45 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 94
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 94 (accept_3_3 35 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45
  94 (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 94 (Polychromatic418967fa.accept_16_1_13_14_1_1064 33 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 94 (accept_3_3 32 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 94
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 94 (accept_3_3 29 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45
  94 (Polychromatic418967fa.accept_20_8_5_14_1_3904 28 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 94 (accept_3_3 26 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 94
  (Polychromatic418967fa.accept_22_2_1_6_1_3903 24 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 94 (accept_3_3 23 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45
  94 (Polychromatic418967fa.accept_13_9_6_3_1_1514 22 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 45 94 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 94 (accept_3_3 20 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 45 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 94 (Polychromatic418967fa.accept_11_7_1_6_1_1281
  18 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 94 (accept_3_3 17 45
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 94 (Polychromatic418967fa.accept_10_6_5_4_1_571
  16 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 94 (accept_3_3 14 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45
  94 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 94 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 94 (accept_3_3 11 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 45 94 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 94 (Polychromatic418967fa.accept_10_9_5_4_1_966 9
  45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 94 (accept_3_3 8 45 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 94
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 94 (accept_3_3 5 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 94
  (Polychromatic418967fa.accept_27_4_18_13_1_3902 4 45 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 94 (accept_3_3 2 45 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 94))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 94
  (allA_of_3_1 44 44 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 94 (allA_succ_of_accept 42 43 94
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 94 (accept_3_3 41 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43
  94 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 43 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 94 (accept_3_3 38 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 43 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 94 (Polychromatic418967fa.accept_15_6_13_4_1_2040
  36 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 94 (accept_3_3 35 43
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 94
  (Polychromatic418967fa.accept_18_16_7_4_1_3901 34 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 43 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 94 (accept_3_3 32 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 43 94 (Polychromatic418967fa.accept_18_13_7_4_1_2738 31 43 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 94 (Polychromatic418967fa.accept_7_2_1_3_1_102 30
  43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 94 (accept_3_3 29 43 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 28
  43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 94 (accept_3_3 26 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43
  94 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 43 94 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 94 (accept_3_3 23 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 43 94 (Polychromatic418967fa.accept_23_22_20_2_1_3900 22 43 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 94 (accept_3_3 20 43 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 94 (Polychromatic418967fa.accept_7_5_1_3_1_103 19
  43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 94
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 94 (accept_3_3 17 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43
  94 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 43 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 94 (accept_3_3 14 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 43 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 94 (Polychromatic418967fa.accept_7_5_1_3_1_103 12
  43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 94 (accept_3_3 11 43 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 10
  43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 94 (accept_3_3 8 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 94
  (Polychromatic418967fa.accept_10_7_3_4_1_978 7 43 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 94 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 94 (accept_3_3 5 43 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 94 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 94 (accept_3_3 2 43 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  94))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 94 (allA_succ_of_accept 41 42 94 (accept_3_3 41 42 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 94 2 20 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 39
  42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 94 2 19 21 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 94
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 94 2 18 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 94 (accept_3_3 35 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 94
  2 17 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42
  94 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 42 94 2 16 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 94 (Polychromatic418967fa.accept_15_1_12_4_1_2022 31 42 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 94 2 15 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 94 (accept_3_3 29 42 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 94 2 14 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 42 94 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 42 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 94 2 13 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 94
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 94 2 12 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 94 (accept_3_3 23 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 94
  2 11 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42
  94 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 94 2 10 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 94 2 9 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 94 (accept_3_3 17 42 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 94 2 8 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 94 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 42 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 94 2 7 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 94 (Polychromatic418967fa.accept_16_13_10_14_1_2871
  13 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 94 2 6 21 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 94 (accept_3_3 11 42
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 94 2 5 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 94
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 94 2 4 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 94 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 94 2 3 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 94 (accept_3_3 5 42 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 94 2 2 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 94 2 1 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  94)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 94 (allA_of_3_1 41 41 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 94 (allA_succ_of_accept 39 40 94 (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 40 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 94 2 19 20 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 94
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 94 2 18 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 40 94 (accept_3_3 35 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 94
  2 17 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40
  94 (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 40 94 2 16 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 40 94 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 40 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 94 2 15 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 94 (accept_3_3 29 40 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 40 94 2 14 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 40 94 (Polychromatic418967fa.accept_31_27_9_1_1_3899 27 40 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 94 2 13 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 94 (Polychromatic418967fa.accept_12_1_4_10_1_209 25
  40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 94 2 12 20 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 94 (accept_3_3 23 40
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 94 2 11 20 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 94
  (Polychromatic418967fa.accept_15_6_10_4_1_150 21 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 94 2 10 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 94 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 40 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 94 2 9 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 94 (accept_3_3 17 40 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 94 2 8 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 94 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 40 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 94 2 7 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 94 (Polychromatic418967fa.accept_12_1_4_10_1_209 13
  40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 94 2 6 20 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 94 (accept_3_3 11 40
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 94 2 5 20 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 94
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 94 2 4 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 94 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 40 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 94 2 3 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 94 (accept_3_3 5 40 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 94 2 2 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 94 (Polychromatic418967fa.accept_17_3_6_9_1_2761 3 40 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 94 2 1 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 94 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 40
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  94)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 94 (allA_succ_of_accept 38 39 94 (accept_3_3 38 39 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 94
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 94 (accept_3_3 35 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39
  94 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 39 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 94 (accept_3_3 32 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 39 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 94 (Polychromatic418967fa.accept_12_6_3_10_1_224
  30 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 94 (accept_3_3 29 39
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 94 (Polychromatic418967fa.accept_9_1_3_4_1_47
  28 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 94
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 94 (accept_3_3 26 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39
  94 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 94 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 94 (accept_3_3 23 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 94 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 39 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 94 (accept_3_3 20 39 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 94
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 94 (accept_3_3 17 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39
  94 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 39 94 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 94 (accept_3_3 14 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 39 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 94 (Polychromatic418967fa.accept_15_12_9_4_1_3898
  12 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 94 (accept_3_3 11 39
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 94 (Polychromatic418967fa.accept_9_1_3_4_1_47
  10 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 94 (accept_3_3 8 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 94
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 94 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 94 (accept_3_3 5 39 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 94 (Polychromatic418967fa.accept_16_4_7_14_1_3897 4 39 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 94 (Polychromatic418967fa.accept_10_3_9_4_1_960 3
  39 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 94 (accept_3_3 2 39 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 94)))))))))))))))))))))))))))))))))))))))
  (allB_succ 38 94 (allA_of_3_1 38 38 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 94 (allA_succ_of_accept
  36 37 94 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 37 94 (accept_3_3 35 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 37 94 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 37 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 94 (accept_3_3 32 37 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 94
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 94 (accept_3_3 29 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37
  94 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 37 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 94 (accept_3_3 26 37 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 37 94 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 37 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 94 (Polychromatic418967fa.accept_9_6_1_4_1_474 24
  37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 94 (accept_3_3 23 37 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 94 (Polychromatic418967fa.accept_7_1_2_3_1_257 22
  37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 94 (accept_3_3 20 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37
  94 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 94 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 37 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 94 (accept_3_3 17 37 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 94 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 94 (accept_3_3 14 37 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 94 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 94
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 94 (accept_3_3 11 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37
  94 (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 94 (accept_3_3 8 37 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 37 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 94 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 37
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 94 (accept_3_3 5 37 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 94 (Polychromatic418967fa.accept_12_4_1_10_1_221 4
  37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 94 (accept_3_3 2 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 94
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 94))))))))))))))))))))))))))))))))))))) (allB_succ 36 94 (allA_succ_of_accept 35 36 94 (accept_3_3 35 36
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 94 2 17 18 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 94
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 94 2 16 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 94 (Polychromatic418967fa.accept_11_9_3_6_1_797 31 36 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 94 2 15 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 94 (accept_3_3 29 36 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 36 94 2 14 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 36 94 (Polychromatic418967fa.accept_21_6_15_10_1_2579 27 36 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 94 2 13 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 94 (Polychromatic418967fa.accept_7_4_1_3_1_277 25
  36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 94 2 12 18 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 94 (accept_3_3 23 36
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 94 2 11 18 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 94
  (Polychromatic418967fa.accept_17_4_2_9_1_3896 21 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 36 94 2 10 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 36 94 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 94 2 9 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 94 (accept_3_3 17 36 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 36 94 2 8 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 36 94 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 36 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 94 2 7 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 94 (Polychromatic418967fa.accept_15_13_6_4_1_1221
  13 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 94 2 6 18 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 94 (accept_3_3 11 36
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 94 2 5 18 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 94
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 94 2 4 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 94 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 36 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 94 2 3 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 94 (accept_3_3 5 36 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 36 94 2 2 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 36 94 (Polychromatic418967fa.accept_21_3_15_10_1_3895 3 36 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 94 2 1 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 94 (Polychromatic418967fa.accept_16_1_4_14_1_1896 1
  36 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 94))))))))))))))))))))))))))))))))))))
  (allB_succ 35 94 (allA_of_3_1 35 35 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 94 (allA_succ_of_accept
  33 34 94 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 34 94 2 16 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 34 94 (Polychromatic418967fa.accept_13_5_8_3_1_1535 31 34 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 94 2 15 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 94 (accept_3_3 29 34 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 94 2 14 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 34 94 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 34 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 94 2 13 17 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 94
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 94 2 12 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 94 (accept_3_3 23 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 94
  2 11 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34
  94 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 94 2 10 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 34 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 94 2 9 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 94 (accept_3_3 17 34 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 94 2 8 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 94 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 34 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 94 2 7 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 94 (Polychromatic418967fa.accept_23_13_11_2_1_3894
  13 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 94 2 6 17 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 94 (accept_3_3 11 34
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 94 2 5 17 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 94
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 34 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 94 2 4 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 94 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 34 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 94 2 3 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 94 (accept_3_3 5 34 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 94 2 2 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 94 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 34 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 94 2 1 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 34
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 94))))))))))))))))))))))))))))))))))
  (allB_succ 33 94 (allA_succ_of_accept 32 33 94 (accept_3_3 32 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 94 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 94 (accept_3_3 29 33 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 28
  33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 94 (accept_3_3 26 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33
  94 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 33 94 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 33 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 94 (accept_3_3 23 33 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 33 94 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 33 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 21
  33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 94 (accept_3_3 20 33 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 94
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 94 (accept_3_3 17 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33
  94 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 33 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 94 (accept_3_3 14 33 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 33 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 12
  33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 94 (accept_3_3 11 33 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 10
  33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 94
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 94 (accept_3_3 8 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 94 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 33 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 94 (accept_3_3 5 33 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 94 (Polychromatic418967fa.accept_13_4_7_3_1_92 4 33 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 94 (accept_3_3 2 33 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 94)))))))))))))))))))))))))))))))))
  (allB_succ 32 94 (allA_of_3_1 32 32 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 94 (allA_succ_of_accept
  30 31 94 (Polychromatic418967fa.accept_19_11_12_18_1_3893 30 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 31 94 (accept_3_3 29 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 31 94 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 31 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 94 (accept_3_3 26 31 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 94
  (Polychromatic418967fa.accept_13_11_5_3_1_889 24 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 94 (accept_3_3 23 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31
  94 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 31 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 94 (accept_3_3 20 31 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 31 94 (Polychromatic418967fa.accept_13_6_5_3_1_426 19 31 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 94 (Polychromatic418967fa.accept_15_3_1_4_1_1246
  18 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 94 (accept_3_3 17 31
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 94
  (Polychromatic418967fa.accept_12_4_7_10_1_563 16 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 31 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 94 (accept_3_3 14 31 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 31 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 94 (Polychromatic418967fa.accept_15_12_1_4_1_2899
  12 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 94 (accept_3_3 11 31
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 94
  (Polychromatic418967fa.accept_16_10_15_14_1_1086 10 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 31 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 94 (accept_3_3 8 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 31 94 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 31 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 94 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 31 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 94 (accept_3_3 5 31 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 94 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 31 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 94 (accept_3_3 2 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 94))))))))))))))))))))))))))))))) (allB_succ 30 94 (allA_succ_of_accept 29 30 94 (accept_3_3 29 30 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 94 2 14 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 94 (Polychromatic418967fa.accept_7_6_2_3_1_107 27
  30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 94 2 13 15 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 94
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 30 94 2 12 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 94 (accept_3_3 23 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 94
  2 11 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30
  94 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 30 94 2 10 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 94 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 94 2 9 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 94 (accept_3_3 17 30 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 94 2 8 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 30 94 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 30 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 94 2 7 15 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 94
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 94 2 6 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 94 (accept_3_3 11 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 94
  2 5 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 94
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 94 2 4 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 94 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 94 2 3 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 94 (accept_3_3 5 30 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 94 2 2 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 94 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 30 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 94 2 1 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 94 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 30
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 94))))))))))))))))))))))))))))))
  (allB_succ 29 94 (allA_of_3_1 29 29 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 94 (allA_succ_of_accept
  27 28 94 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 28 94 2 13 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 28 94 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 94 2 12 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 94 (accept_3_3 23 28 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 94 2 11 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 28 94 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 28 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 94 2 10 14 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 94
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 94 2 9 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 94 (accept_3_3 17 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 94
  2 8 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28
  94 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 94 2 7 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 94 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 28 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 94 2 6 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 94 (accept_3_3 11 28 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 28 94 2 5 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 28 94 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 28 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 94 2 4 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 94 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 94 2 3 14 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 94 (accept_3_3 5 28
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 94 2 2 14 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 94
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 28 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 94 2 1 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 94 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 28 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 94)))))))))))))))))))))))))))) (allB_succ 27 94 (allA_succ_of_accept 26
  27 94 (accept_3_3 26 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 94 (Polychromatic418967fa.accept_13_11_1_3_1_910 24 27 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 94 (accept_3_3 23 27 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 27 94 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 27 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 94 (accept_3_3 20 27 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 94
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 94 (accept_3_3 17 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27
  94 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 27 94 (Polychromatic418967fa.accept_13_2_1_3_1_419 15 27 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 94 (accept_3_3 14 27 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 27 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 94 (Polychromatic418967fa.accept_10_2_7_4_1_967 12
  27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 94 (accept_3_3 11 27 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 94 (Polychromatic418967fa.accept_11_10_5_6_1_1842
  10 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 94 (accept_3_3 8 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 94
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 94 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 27 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 94 (accept_3_3 5 27 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 94 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 94 (Polychromatic418967fa.accept_10_3_7_4_1_584 3
  27 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 94 (accept_3_3 2 27 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 94))))))))))))))))))))))))))) (allB_succ
  26 94 (allA_of_3_1 26 26 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 94 (allA_succ_of_accept 24 25 94
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 94 (accept_3_3 23 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25
  94 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 25 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 94 (accept_3_3 20 25 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 25 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 94 (Polychromatic418967fa.accept_17_1_8_9_1_1810
  18 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 94 (accept_3_3 17 25
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 94 (Polychromatic418967fa.accept_10_6_5_4_1_571
  16 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 94 (accept_3_3 14 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25
  94 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 25 94 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 25 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 94 (accept_3_3 11 25 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 25 94 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 25 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 94 (accept_3_3 8 25 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 94
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 94 (accept_3_3 5 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 94
  (Polychromatic418967fa.accept_12_4_1_10_1_221 4 25 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 94 (accept_3_3 2 25 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 94 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 94))))))))))))))))))))))))) (allB_succ 24 94
  (allA_succ_of_accept 23 24 94 (accept_3_3 23 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 94
  2 11 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24
  94 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 94 2 10 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 24 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 94 2 9 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 94 (accept_3_3 17 24 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 94 2 8 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 94 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 24 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 94 2 7 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 94 (Polychromatic418967fa.accept_15_13_9_4_1_3892
  13 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 94 2 6 12 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 94 (accept_3_3 11 24
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 94 2 5 12 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 94
  (Polychromatic418967fa.accept_19_9_5_18_1_3891 9 24 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 94 2 4 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 94 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 94 2 3 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 94 (accept_3_3 5 24 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 94 2 2 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 94 2 1 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 24
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 94)))))))))))))))))))))))) (allB_succ 23
  94 (allA_of_3_1 23 23 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 94 (allA_succ_of_accept 21 22 94
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 22 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 94 2 10 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 94 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 22 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 94 2 9 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 94 (accept_3_3 17 22 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 94 2 8 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 94 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 22 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 94 2 7 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 94 (Polychromatic418967fa.accept_17_13_5_9_1_1762
  13 22 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 94 2 6 11 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 94 (accept_3_3 11 22
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 94 2 5 11 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 94
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 22 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 94 2 4 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 94 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 22 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 94 2 3 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 94 (accept_3_3 5 22 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 94 2 2 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 94 (Polychromatic418967fa.accept_15_3_7_4_1_1225 3 22 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 94 2 1 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 94 (Polychromatic418967fa.accept_23_1_22_2_1_3890 1
  22 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 94)))))))))))))))))))))) (allB_succ 21
  94 (allA_succ_of_accept 20 21 94 (accept_3_3 20 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  21 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 94 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 94 (accept_3_3 17 21 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 94 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 21 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 94 (accept_3_3 14 21 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 94
  (Polychromatic418967fa.accept_17_12_4_9_1_3889 12 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 94 (accept_3_3 11 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21
  94 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 21 94 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 21 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 94 (accept_3_3 8 21 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 21 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 94 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 94 (accept_3_3 5 21 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 94 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4
  21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 94 (accept_3_3 2 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 94
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 94))))))))))))))))))))) (allB_succ 20 94 (allA_of_3_1 20 20 94 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 19 94 (allA_succ_of_accept 18 19 94 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 19 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 94 (accept_3_3 17 19 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 94 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 19 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 94 (accept_3_3 14 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19
  94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 19 94 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 94 (accept_3_3 11 19 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 19 94 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 19 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 94 (accept_3_3 8 19 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 94 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 94
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 94 (accept_3_3 5 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 94
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 19 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 94 (accept_3_3 2 19 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 94))))))))))))))))))) (allB_succ 18 94 (allA_succ_of_accept 17
  18 94 (accept_3_3 17 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 94 2 8 9 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 94
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 94 2 7 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 94 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 18 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 94 2 6 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 94 (accept_3_3 11 18 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 94 2 5 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 94 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 18 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 94 2 4 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 94 (Polychromatic418967fa.accept_14_7_4_10_1_1351 7
  18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 94 2 3 9 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 94 (accept_3_3 5 18
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 94 2 2 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 94 (Polychromatic418967fa.accept_12_3_6_10_1_576 3
  18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 18 94 2 1 9 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 94
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 18 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 94)))))))))))))))))) (allB_succ 17 94 (allA_of_3_1 17 17 94 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 94 (allA_succ_of_accept 15 16 94 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 16 94 2 7 8 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 16 94
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 16 94 2 6 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 16 94 (accept_3_3 11 16 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16 94
  2 5 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 16 94
  (Polychromatic418967fa.accept_19_9_16_18_1_3887 9 16 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 16 94 2 4 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 16 94 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 16 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 94 2 3 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 94 (accept_3_3 5 16 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 16 94 2 2 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 16 94 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 16 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 94 2 1 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 94 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 16
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 94)))))))))))))))) (allB_succ 15 94
  (allA_succ_of_accept 14 15 94 (accept_3_3 14 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15
  94 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 94 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 94 (accept_3_3 11 15 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 15 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 94 (accept_3_3 8 15 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 94
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 94 (accept_3_3 5 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 94
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 15 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 94 (accept_3_3 2 15 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 94))))))))))))))) (allB_succ 14 94 (allA_of_3_1 14 14 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 94 (allA_succ_of_accept 12 13 94
  (Polychromatic418967fa.accept_19_12_13_18_1_3886 12 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 94 (accept_3_3 11 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  94 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 94 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 94 (accept_3_3 8 13 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 94 (Polychromatic418967fa.accept_15_6_13_4_1_2040 6
  13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 94 (accept_3_3 5 13 94
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 94 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 94
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 94 (accept_3_3 2 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 94
  (Polychromatic418967fa.accept_16_1_13_14_1_1064 1 13 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 94))))))))))))) (allB_succ 12 94 (allA_succ_of_accept 11 12 94 (accept_3_3 11 12 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 94 2 5 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 12 94 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 94 2 4 6 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 94
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 94 2 3 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 94 (accept_3_3 5 12 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 94 2
  2 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 94
  (Polychromatic418967fa.accept_21_3_12_10_1_3885 3 12 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 12 94 2 1 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 94 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 94)))))))))))) (allB_succ 11 94 (allA_of_3_1 11 11 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 10 94 (allA_succ_of_accept 9 10 94 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 10
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 94 2 4 5 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 94
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 94 2 3 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 94 (accept_3_3 5 10 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 94 2
  2 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 94
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 10 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 94 2 1 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 94 (Polychromatic418967fa.accept_17_1_10_9_1_3884 1 10 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 94)))))))))) (allB_succ 9 94 (allA_succ_of_accept 8 9 94 (accept_3_3 8 9
  94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9
  94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 94
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 94 (accept_3_3 5 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 94
  (Polychromatic418967fa.accept_16_4_9_14_1_3883 4 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 94 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 94 (accept_3_3 2 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 94 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 9 94))))))))) (allB_succ 8 94 (allA_of_3_1 8 8 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 7 94 (allA_succ_of_accept 6 7 94 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 94 (accept_3_3 5 7 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 94 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 7 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 94
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 7 94 (accept_3_3 2 7 94 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 94
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 7 94))))))) (allB_succ 6 94 (allA_succ_of_accept 5 6 94 (accept_3_3 5 6 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 6 94 2 2 3 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 6 94 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 6 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 94 2 1 3 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 94 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 6 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 94)))))) (allB_succ 5 94 (allA_of_3_1 5 5 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 94 (allA_succ_of_accept 3 4 94
  (Polychromatic418967fa.accept_19_3_4_18_1_3882 3 4 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 4 94 2 1 2 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 4 94 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 4 94)))) (allB_succ 3 94 (allA_succ_of_accept 2 3 94 (accept_3_3 2 3 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 94 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 94))) (allB_succ 2 94 (allA_of_3_1 2 2 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_two
  94))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


