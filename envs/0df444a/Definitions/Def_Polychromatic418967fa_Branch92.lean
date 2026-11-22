-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch92
-- name    : Polychromatic418967fa_Branch92
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:23.36603+00:00
-- url     : https://prove2.me/theorems/cf63b17d-aed4-45b3-be98-c7db8934e271
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

def Polychromatic418967fa.branch_92 : allB 92 92 :=
  allB_succ' 2 91 92 (Eq.refl Bool.true) (allA_of_3_0 2 91 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3 90
  92 (Eq.refl Bool.true) (allA_succ_of_gcd 2 90 92 2 1 45 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 90 92 (accept_3_2 1 90 92 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 92))) (allB_succ' 4 89 92 (Eq.refl Bool.true) (allA_succ_of_accept 3 89 92
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 92 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 89 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 92 (accept_3_2 1 89 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 92)))) (allB_succ' 5 88 92 (Eq.refl Bool.true) (allA_of_3_0 5 88 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 87 92 (Eq.refl Bool.true) (allA_succ_of_accept 5 87 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 92 (accept_3_2 4 87 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 92
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 92 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 87 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 92 (accept_3_2 1 87 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 92)))))) (allB_succ' 7 86 92 (Eq.refl Bool.true) (allA_succ_of_gcd 6 86 92 2 3 43 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 86 92
  (Polychromatic418967fa.accept_12_5_2_8_1_172 5 86 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 86 92 2 2 43 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 86 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 86 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 92 2 1 43 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 92 (accept_3_2 1 86 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 92))))))) (allB_succ' 8 85 92 (Eq.refl Bool.true) (allA_of_3_0 8 85 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 9 84 92 (Eq.refl Bool.true) (allA_succ_of_gcd 8 84 92 4 2 21 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 92 (accept_3_2 7 84 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 92 2 3 42 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 92 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 92 4 1 21 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 92
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 84 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 84 92 2 1 42 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 92 (accept_3_2 1 84 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 92)))))))))
  (allB_succ' 10 83 92 (Eq.refl Bool.true) (allA_succ_of_accept 9 83 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 92
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 83 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 92 (accept_3_2 7 83 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 92
  (Polychromatic418967fa.accept_13_6_5_1_1_834 6 83 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 92 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 83 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 92 (accept_3_2 4 83 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 92 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 83
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 92 (accept_3_2 1 83 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83 92)))))))))) (allB_succ' 11 82 92 (Eq.refl Bool.true)
  (allA_of_3_0 11 82 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 81 92 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 81 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 92 (accept_3_2 10 81 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 81 92 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 81 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 92 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8
  81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 92 (accept_3_2 7 81 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 92 (Polychromatic418967fa.accept_10_6_1_2_1_874 6
  81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 92 (accept_3_2 4 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 92
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 92 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 81 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 92 (accept_3_2 1 81 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 92)))))))))))) (allB_succ' 13 80 92 (Eq.refl Bool.true) (allA_succ_of_gcd 12 80 92 4 3 20 23
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 92
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 80 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 92 2 5 40 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 92 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 80 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 92 4 2 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 92 (accept_3_2 7 80 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 80 92 2 3 40 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 80 92 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 80 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 92 4 1 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 92 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 80
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 92 2 1 40 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 92 (accept_3_2 1 80
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80 92))))))))))))) (allB_succ' 14 79 92 (Eq.refl Bool.true)
  (allA_of_3_0 14 79 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 78 92 (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 78 92 2 7 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 92 (accept_3_2 13 78 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 92
  2 6 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78
  92 (Polychromatic418967fa.accept_19_11_2_16_1_3822 11 78 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 92 2 5 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 92 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 78 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 92 2 4 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 92 (accept_3_2 7 78 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 78 92 2 3 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 92 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 78 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 92 2 2 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 78
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 92 2 1 39 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 92 (accept_3_2 1 78
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 92))))))))))))))) (allB_succ' 16 77 92 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 77 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 92 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 77 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 92 (accept_3_2 13 77 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 92 (Polychromatic418967fa.accept_9_3_5_2_1_28 12
  77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 92
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 92 (accept_3_2 10 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 77 92 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 92 (accept_3_2 7 77 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 77 92 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 92 (Polychromatic418967fa.accept_10_5_7_2_1_516 5
  77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 92 (accept_3_2 4 77 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 92
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 92 (accept_3_2 1 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  92)))))))))))))))) (allB_succ' 17 76 92 (Eq.refl Bool.true) (allA_of_3_0 17 76 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 75 92 (Eq.refl Bool.true) (allA_succ_of_accept 17 75 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 92 (accept_3_2 16 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75
  92 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 92 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 75 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 92 (accept_3_2 13 75 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 92 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 75 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 92 (accept_3_2 10 75 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 92 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9
  75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 92
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 92 (accept_3_2 7 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 92
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 92 (accept_3_2 4 75 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 92 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 92 (Polychromatic418967fa.accept_11_2_9_4_1_310 2
  75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 92 (accept_3_2 1 75 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 92)))))))))))))))))) (allB_succ' 19 74 92 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 74 92 2 9 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 92 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 74 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 92 2 8 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 92 (Polychromatic418967fa.accept_13_2_9_1_1_67 15 74 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 92 2 7 37 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 92 (accept_3_2 13 74 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 92 2 6 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 92 (Polychromatic418967fa.accept_12_11_2_8_1_511 11
  74 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 92 2 5 37 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 92
  (Polychromatic418967fa.accept_22_9_8_4_1_3821 9 74 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 74 92 2 4 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 74 92 (accept_3_2 7 74 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 92 2
  3 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74 92
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 74 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 74 92 2 2 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 74 92 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 74 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 92 2 1 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 92 (accept_3_2 1 74 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 92))))))))))))))))))) (allB_succ' 20 73 92 (Eq.refl Bool.true) (allA_of_3_0 20 73 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 72 92 (Eq.refl Bool.true) (allA_succ_of_gcd 20 72 92 4 5 18 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 92 (accept_3_2 19 72
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 92 2 9 36 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 92
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 72 92 4 4 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 72 92 (Polychromatic418967fa.accept_14_1_2_8_1_655 15 72 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 92 2 7 36 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 92 (accept_3_2 13 72 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 72 92 4 3 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 72 92 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 72 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 92 2 5 36 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 92 (Polychromatic418967fa.accept_16_9_8_12_1_979 9
  72 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 92 4 2 18 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 92 (accept_3_2 7 72
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 92 2 3 36 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 92
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 72 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 92 4 1 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 72 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 92 2 1 36 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 92 (accept_3_2 1 72 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 92))))))))))))))))))))) (allB_succ' 22 71 92 (Eq.refl Bool.true) (allA_succ_of_accept 21 71
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 71 92 (Polychromatic418967fa.accept_13_7_6_1_1_368 20 71 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 92 (accept_3_2 19 71 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 71 92 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 71 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 92
  (Polychromatic418967fa.accept_19_17_14_16_1_3820 17 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 92 (accept_3_2 16 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 71 92 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 92 (accept_3_2 13 71 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 71 92 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 71 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 92 (Polychromatic418967fa.accept_8_3_7_4_1_42 11
  71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 92 (accept_3_2 10 71 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 92
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 92 (accept_3_2 7 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 92
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 92 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 71 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 92 (accept_3_2 4 71 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 92 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 92 (accept_3_2 1 71 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 92)))))))))))))))))))))) (allB_succ' 23 70 92 (Eq.refl
  Bool.true) (allA_of_3_0 23 70 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 69 92 (Eq.refl Bool.true)
  (allA_succ_of_gcd 23 69 92 23 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 22 69 92 (accept_3_2 22 69 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69
  92 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 92 (Polychromatic418967fa.accept_16_4_5_12_1_2749 20 69 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 92 (accept_3_2 19 69 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 92 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 69 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 17
  69 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 92 (accept_3_2 16 69 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 92
  (Polychromatic418967fa.accept_19_15_12_16_1_3819 15 69 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 92 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 69 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 92 (accept_3_2 13 69 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 92 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  69 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 92 (accept_3_2 10 69 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 92 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 92
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 69 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 92 (accept_3_2 7 69 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 92
  (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 92 (accept_3_2 4 69 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 69 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 92 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 69
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 92 (accept_3_2 1 69 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 92)))))))))))))))))))))))) (allB_succ' 25 68 92 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 68 92 4 6 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 68 92 (Polychromatic418967fa.accept_16_7_4_12_1_1806 23 68 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 92 2 11 34 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 92 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 68
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 92 4 5 17 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 92 (accept_3_2 19 68
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 92 2 9 34 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68 92
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 68 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 68 92 4 4 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 68 92 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 68 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 92 2 7 34 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 92 (accept_3_2 13 68 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 68 92 4 3 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 68 92 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 68 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 92 2 5 34 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 92 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 68
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 92 4 2 17 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 92 (accept_3_2 7 68
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 92 2 3 34 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68 92
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 92 4 1 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 92 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 68 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 92 2 1 34 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 92 (accept_3_2 1 68 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 92))))))))))))))))))))))))) (allB_succ' 26 67 92 (Eq.refl Bool.true) (allA_of_3_0 26 67 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 66 92 (Eq.refl Bool.true) (allA_succ_of_gcd 26 66 92 2 13 33
  46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 92
  (accept_3_2 25 66 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 92 2 12 33 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 92
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 66 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 92 2 11 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 66 92 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 66 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 92 2 10 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 92 (accept_3_2 19 66 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 66 92 2 9 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 66 92 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 92 2 8 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 92 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  66 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 92 2 7 33 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 92 (accept_3_2 13 66
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 92 2 6 33 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 92
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 66 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 92 2 5 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 92 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 92 2 4 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 92 (accept_3_2 7 66 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 92 2 3 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 92 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 92 2 2 33 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 92 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 66
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 92 2 1 33 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 92 (accept_3_2 1 66
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 92))))))))))))))))))))))))))) (allB_succ' 28 65 92 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 65 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 92 (Polychromatic418967fa.accept_12_2_5_8_1_159 26
  65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 92 (accept_3_2 25 65 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 24
  65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 92
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 92 (accept_3_2 22 65 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 65 92 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 65 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 92 (accept_3_2 19 65 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 65 92 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 65 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 92 (accept_3_2 16 65 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 92
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 92 (accept_3_2 13 65 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65
  92 (Polychromatic418967fa.accept_15_12_5_2_1_2786 12 65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 92 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 65 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 92 (accept_3_2 10 65 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 92
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 92 (accept_3_2 7 65 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 92
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 92 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 65 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 92 (accept_3_2 4 65 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 92 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  65 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 92 (accept_3_2 1 65 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 92)))))))))))))))))))))))))))) (allB_succ' 29 64 92 (Eq.refl
  Bool.true) (allA_of_3_0 29 64 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 63 92 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 92 (accept_3_2 28 63 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 63 92 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 92 (Polychromatic418967fa.accept_19_7_6_16_1_3818
  26 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 92 (accept_3_2 25 63
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 92
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 92 (accept_3_2 22 63 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 63 92 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 63 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 92 (Polychromatic418967fa.accept_13_7_11_1_1_2903
  20 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 92 (accept_3_2 19 63
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 92 (Polychromatic418967fa.accept_11_7_8_4_1_718
  18 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 92 (accept_3_2 16 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63
  92 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 92 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 63 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 92 (accept_3_2 13 63 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 92 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 63 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 92 (accept_3_2 10 63 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 92 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9
  63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 92
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 92 (accept_3_2 7 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 92
  (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 92 (accept_3_2 4 63 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 92 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 92 (Polychromatic418967fa.accept_16_2_15_12_1_1744
  2 63 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 92 (accept_3_2 1 63 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 92)))))))))))))))))))))))))))))) (allB_succ' 31 62 92 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 62 92 2 15 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 92 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 62 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 92 2 14 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 92 (Polychromatic418967fa.accept_19_8_5_16_1_2589
  27 62 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 92 2 13 31 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 92 (accept_3_2 25 62
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 92 2 12 31 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 92
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 62 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 92 2 11 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 92 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 62 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 92 2 10 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 92 (accept_3_2 19 62 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 62 92 2 9 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 62 92 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 62 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 92 2 8 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 92 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  62 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 92 2 7 31 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 92 (accept_3_2 13 62
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 92 2 6 31 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 92
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 62 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 92 2 5 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 92 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 62 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 92 2 4 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 92 (accept_3_2 7 62 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 92 2 3 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 92 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 62 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 92 2 2 31 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 92 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 62
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 92 2 1 31 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 92 (accept_3_2 1 62
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 92))))))))))))))))))))))))))))))) (allB_succ' 32 61 92
  (Eq.refl Bool.true) (allA_of_3_0 32 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 60 92 (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 60 92 4 8 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 60 92 (accept_3_2 31 60 92 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 92 2 15 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 92 (Polychromatic418967fa.accept_24_5_12_20_1_3817 29 60 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 92 4 7 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 92 (Polychromatic418967fa.accept_18_9_6_2_1_2619 27 60 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 92 2 13 30 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 92 (accept_3_2 25 60 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 92 4 6 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 92 (Polychromatic418967fa.accept_9_5_6_2_1_161 23
  60 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 92 2 11 30 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 92
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 92 4 5 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 92 (accept_3_2 19 60 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 92
  2 9 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60
  92 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 60 92 4 4 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 60 92 (Polychromatic418967fa.accept_17_15_9_7_1_3816 15 60 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 92 2 7 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 92 (accept_3_2 13 60 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 60 92 4 3 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 60 92 (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 60 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 92 2 5 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 92 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 60
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 92 4 2 15 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 92 (accept_3_2 7 60
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 92 2 3 30 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 92
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 60 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 92 4 1 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 92 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 92 2 1 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 92 (accept_3_2 1 60 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 92))))))))))))))))))))))))))))))))) (allB_succ' 34 59 92 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 59 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 92 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 59 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 92 (accept_3_2 31 59 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 92 (Polychromatic418967fa.accept_7_2_3_1_1_10 30
  59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 92
  (Polychromatic418967fa.accept_13_3_7_1_1_334 29 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 92 (accept_3_2 28 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 59
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 59 92 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 59 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 92 (accept_3_2 25 59 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 59 92 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 92 (Polychromatic418967fa.accept_7_2_3_1_1_10 23
  59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 92 (accept_3_2 22 59 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 92
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 92 (accept_3_2 19 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59
  92 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 59 92 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 92 (accept_3_2 16 59 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 59 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 92 (Polychromatic418967fa.accept_12_2_11_8_1_504
  14 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 92 (accept_3_2 13 59
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 92 (Polychromatic418967fa.accept_7_5_3_1_1_424
  12 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 92
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 92 (accept_3_2 10 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 92 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 59 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 92 (accept_3_2 7 59 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 92 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 59 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 92 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 59
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 92 (accept_3_2 4 59 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 92
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 92 (accept_3_2 1 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  92)))))))))))))))))))))))))))))))))) (allB_succ' 35 58 92 (Eq.refl Bool.true) (allA_of_3_0 35 58 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 57 92 (Eq.refl Bool.true) (allA_succ_of_accept 35 57 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 92 (accept_3_2 34 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57
  92 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 92 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 57 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 92 (accept_3_2 31 57 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 92 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 57 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 92 (accept_3_2 28 57 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 92 (Polychromatic418967fa.accept_18_9_3_2_1_3814
  27 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 92
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 92 (accept_3_2 25 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57
  92 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 92 (accept_3_2 22 57 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 92 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 92 (Polychromatic418967fa.accept_11_9_2_4_1_707 20
  57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 92 (accept_3_2 19 57 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 92 (Polychromatic418967fa.accept_12_6_9_8_1_165 18
  57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 92 (accept_3_2 16 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57
  92 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 92 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 57 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 92 (accept_3_2 13 57 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 92 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 57 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 92 (accept_3_2 10 57 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 92 (Polychromatic418967fa.accept_10_9_7_2_1_887 9
  57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 92
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 92 (accept_3_2 7 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 92
  (Polychromatic418967fa.accept_9_6_3_2_1_431 6 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 92 (accept_3_2 4 57 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 92 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 57 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 92 (Polychromatic418967fa.accept_14_2_1_8_1_650 2
  57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 92 (accept_3_2 1 57 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 92)))))))))))))))))))))))))))))))))))) (allB_succ' 37 56 92
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 56 92 4 9 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 56 92 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 56 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 92 2 17 28 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 92
  (Polychromatic418967fa.accept_16_1_8_12_1_405 33 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 92 4 8 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 92 (accept_3_2 31 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 92
  2 15 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56
  92 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 92 4 7 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 92 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 56 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 92 2 13 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 92 (accept_3_2 25 56 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 56 92 4 6 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 56 92 (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 56 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 92 2 11 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 92 (Polychromatic418967fa.accept_10_1_6_2_1_867 21
  56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 92 4 5 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 92 (accept_3_2 19 56
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 92 2 9 28 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 92
  (Polychromatic418967fa.accept_16_1_8_12_1_405 17 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 56 92 4 4 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 56 92 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 56 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 92 2 7 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 92 (accept_3_2 13 56 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 56 92 4 3 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 56 92 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 92 2 5 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 92 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9
  56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 92 4 2 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 92 (accept_3_2 7 56
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 92 2 3 28 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56 92
  (Polychromatic418967fa.accept_13_5_4_1_1_364 5 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 92 4 1 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 92 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 56 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 92 2 1 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 92 (accept_3_2 1 56 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 92))))))))))))))))))))))))))))))))))))) (allB_succ' 38 55 92 (Eq.refl Bool.true) (allA_of_3_0
  38 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 54 92 (Eq.refl Bool.true) (allA_succ_of_gcd 38 54 92
  2 19 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54
  92 (accept_3_2 37 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 92 2 18 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 92
  (Polychromatic418967fa.accept_13_9_2_1_1_813 35 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 92 2 17 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 92 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 92 2 16 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 92 (accept_3_2 31 54 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 54 92 2 15 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 92 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 54 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 92 2 14 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 92 (Polychromatic418967fa.accept_7_6_5_1_1_416 27
  54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 92 2 13 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 92 (accept_3_2 25 54
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 92 2 12 27 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 92
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 92 2 11 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 54 92 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 92 2 10 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 92 (accept_3_2 19 54 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 54 92 2 9 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 54 92 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 54 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 92 2 8 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 92 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 92 2 7 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 92 (accept_3_2 13 54
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 92 2 6 27 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 92
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 92 2 5 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 54 92 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 54 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 92 2 4 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 92 (accept_3_2 7 54 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 54 92 2 3 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 54 92 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 54 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 92 2 2 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 92 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 54
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 92 2 1 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 92 (accept_3_2 1 54
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 92))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 53
  92 (Eq.refl Bool.true) (allA_succ_of_accept 39 53 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 92
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 92 (accept_3_2 37 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53
  92 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 53 92 (Polychromatic418967fa.accept_10_5_3_2_1_899 35 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 92 (accept_3_2 34 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 53 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 92 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 92 (accept_3_2 31 53 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 92 (Polychromatic418967fa.accept_9_3_8_2_1_162 30
  53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 92
  (Polychromatic418967fa.accept_17_12_2_7_1_3813 29 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 92 (accept_3_2 28 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 53 92 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 92 (accept_3_2 25 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 53 92 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 92 (Polychromatic418967fa.accept_9_5_8_2_1_409 23
  53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 92 (accept_3_2 22 53 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 92
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 20 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 92 (accept_3_2 19 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53
  92 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 92 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 92 (accept_3_2 16 53 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 92
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 92 (accept_3_2 13 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53
  92 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 53 92 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 92 (accept_3_2 10 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 53 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 92 (Polychromatic418967fa.accept_16_8_5_12_1_3812 8
  53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 92 (accept_3_2 7 53 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 92 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 53
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 92
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 92 (accept_3_2 4 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 92
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 92 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 92 (accept_3_2 1 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 92)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 52 92 (Eq.refl Bool.true)
  (allA_of_3_0 41 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 51 92 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 51 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 92 (accept_3_2 40 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 92 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 92 (accept_3_2 37 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 92 (Polychromatic418967fa.accept_10_6_1_2_1_874 36
  51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 92 (accept_3_2 34 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51
  92 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 92 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 92 (accept_3_2 31 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 92 (accept_3_2 28 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 92 (Polychromatic418967fa.accept_7_6_2_1_1_214 27
  51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 92
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 92 (accept_3_2 25 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51
  92 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 92 (accept_3_2 22 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 92 (Polychromatic418967fa.accept_7_6_2_1_1_214 20
  51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 92 (accept_3_2 19 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 92 (Polychromatic418967fa.accept_12_6_3_8_1_512 18
  51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 92 (accept_3_2 16 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51
  92 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 92 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 92 (accept_3_2 13 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 51 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 92 (accept_3_2 10 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 92 (Polychromatic418967fa.accept_10_9_1_2_1_522 9
  51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 92
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 92 (accept_3_2 7 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 92
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 92 (accept_3_2 4 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 92 (Polychromatic418967fa.accept_13_2_12_1_1_343 2
  51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 92 (accept_3_2 1 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 92)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 50
  92 (Eq.refl Bool.true) (allA_succ_of_gcd 42 50 92 2 21 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 92 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 92 2 20 25 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 92
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 92 2 19 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 50 92 (accept_3_2 37 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 92
  2 18 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50
  92 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 50 92 2 17 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 50 92 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 50 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 92 2 16 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 92 (accept_3_2 31 50 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 50 92 2 15 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 92 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 92 2 14 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 92 (Polychromatic418967fa.accept_15_12_5_2_1_2786
  27 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 92 2 13 25 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 92 (accept_3_2 25 50
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 92 2 12 25 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 92
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 92 2 11 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 92 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 50 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 92 2 10 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 92 (accept_3_2 19 50 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 50 92 2 9 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 50 92 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 50 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 92 2 8 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 92 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 92 2 7 25 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 92 (accept_3_2 13 50
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 92 2 6 25 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 92
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 92 2 5 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 92 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 50 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 92 2 4 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 92 (accept_3_2 7 50 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 92 2 3 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 92 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 50 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 92 2 2 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 92 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 50
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 92 2 1 25 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 92 (accept_3_2 1 50
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 92))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44
  49 92 (Eq.refl Bool.true) (allA_of_3_0 44 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 48 92 (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 48 92 4 11 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 48 92 (accept_3_2 43 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 92 2 21 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 92 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 92 4 10 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 92 (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 48 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 92 2 19 24 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 92 (accept_3_2 37 48 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 92 4 9 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 92 (Polychromatic418967fa.accept_9_8_3_2_1_417 35
  48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 92 2 17 24 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 92
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 92 4 8 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 92 (accept_3_2 31 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 92
  2 15 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48
  92 (Polychromatic418967fa.accept_15_14_3_2_1_2811 29 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 92 4 7 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 92 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 48 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 92 2 13 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 92 (accept_3_2 25 48 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 92 4 6 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 48 92 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 92 2 11 24 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 92
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 92 4 5 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 92 (accept_3_2 19 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 92
  2 9 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48
  92 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 48 92 4 4 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 48 92 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 92 2 7 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 92 (accept_3_2 13 48 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 48 92 4 3 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 48 92 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 48 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 92 2 5 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 92 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 92 4 2 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 92 (accept_3_2 7 48
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 92 2 3 24 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 92
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 92 4 1 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 92 (Polychromatic418967fa.accept_18_3_12_2_1_2639 3 48 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 92 2 1 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 92 (accept_3_2 1 48 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 92))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 47 92 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 47 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 92 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 47 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 92 (accept_3_2 43 47 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 92 (Polychromatic418967fa.accept_19_4_9_16_1_3811
  42 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 92
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 92 (accept_3_2 40 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 92 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 47 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 92 (accept_3_2 37 47 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 92 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 47 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 92 (Polychromatic418967fa.accept_8_3_7_4_1_42 35
  47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 92 (accept_3_2 34 47 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 92
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 92 (accept_3_2 31 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47
  92 (Polychromatic418967fa.accept_25_5_22_17_1_3810 30 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 92 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 47 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 92 (accept_3_2 28 47 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 92
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 92 (accept_3_2 25 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47
  92 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 47 92 (Polychromatic418967fa.accept_17_6_13_7_1_272 23 47 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 92 (accept_3_2 22 47 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 47 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 92 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 92 (accept_3_2 19 47 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 92 (Polychromatic418967fa.accept_7_4_5_1_1_418 18
  47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 92
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 92 (accept_3_2 16 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 92 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 47 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 92 (accept_3_2 13 47 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 92 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 47 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 92 (Polychromatic418967fa.accept_7_4_5_1_1_418 11
  47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 92 (accept_3_2 10 47 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 92
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 8 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 92 (accept_3_2 7 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 92
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 92 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 47 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 92 (accept_3_2 4 47 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 92 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  47 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 92 (accept_3_2 1 47 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 92)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  92 (allA_of_3_0 46 46 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 92 (allA_succ_of_accept 44 45 92
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 92 (accept_3_2 43 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45
  92 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 92 (accept_3_2 40 45 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 92 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 45 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 92 (Polychromatic418967fa.accept_10_8_5_2_1_881 38
  45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 92 (accept_3_2 37 45 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 92 (Polychromatic418967fa.accept_16_4_13_12_1_1740
  36 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 92 (accept_3_2 34 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45
  92 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 92 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 45 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 92 (accept_3_2 31 45 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 45 92 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 45 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 92 (accept_3_2 28 45 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 92 (Polychromatic418967fa.accept_10_7_5_2_1_880 27
  45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 92
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 92 (accept_3_2 25 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45
  92 (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 92 (accept_3_2 22 45 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 92 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 45 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 92
  (Polychromatic418967fa.accept_13_7_6_1_1_368 20 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 92 (accept_3_2 19 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45
  92 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 92 (accept_3_2 16 45 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 92 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 45 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 92 (Polychromatic418967fa.accept_21_14_3_8_1_3806
  14 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 92 (accept_3_2 13 45
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 92 (Polychromatic418967fa.accept_7_5_3_1_1_424
  12 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 92 (accept_3_2 10 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45
  92 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 92 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 45 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 92 (accept_3_2 7 45 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 92 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 45 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 92 (accept_3_2 4 45 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 92 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 45
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 92
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 92 (accept_3_2 1 45 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  92))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 92 (allA_succ_of_accept 43 44 92 (accept_3_2 43 44 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 92 2 21 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 92 (Polychromatic418967fa.accept_7_6_2_1_1_214 41
  44 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 92 4 10 11 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 92
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 44 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 44 92 2 19 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 44 92 (accept_3_2 37 44 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 92
  4 9 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44
  92 (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 44 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 92 2 17 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 44 92 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 44 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 92 4 8 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 92 (accept_3_2 31 44 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 44 92 2 15 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 44 92 (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 44 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 92 4 7 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 92 (Polychromatic418967fa.accept_7_6_2_1_1_214 27
  44 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 92 2 13 22 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 92 (accept_3_2 25 44
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 92 4 6 11 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 92
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 92 2 11 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 92 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 44 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 92 4 5 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 92 (accept_3_2 19 44 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 44 92 2 9 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 44 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 44 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 92 4 4 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 92 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  44 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 92 2 7 22 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 92 (accept_3_2 13 44
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 92 4 3 11 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 92
  (Polychromatic418967fa.accept_19_11_6_16_1_3805 11 44 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 44 92 2 5 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 44 92 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 44 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 92 4 2 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 92 (accept_3_2 7 44 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 44 92 2 3 22 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 44 92 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 92 4 1 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 44
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 92 2 1 22 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 92 (accept_3_2 1 44
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 92)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  92 (allA_of_3_0 43 43 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 92 (allA_succ_of_accept 41 42 92
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 92 2 20 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 92 2 19 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 92 (accept_3_2 37 42 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 42 92 2 18 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 42 92 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 42 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 92 2 17 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 92 (Polychromatic418967fa.accept_12_9_6_8_1_518 33
  42 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 92 2 16 21 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 92 (accept_3_2 31 42
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 92 2 15 21 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 92
  (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 42 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 92 2 14 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 42 92 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 42 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 92 2 13 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 92 (accept_3_2 25 42 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 42 92 2 12 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 92 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 92 2 11 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 21
  42 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 92 2 10 21 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 92 (accept_3_2 19 42
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 92 2 9 21 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 92
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 92 2 8 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 42 92 (Polychromatic418967fa.accept_12_3_6_8_1_969 15 42 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 92 2 7 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 92 (accept_3_2 13 42 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 42 92 2 6 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 42 92 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 42 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 92 2 5 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 92 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 92 2 4 21 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 92 (accept_3_2 7 42
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 92 2 3 21 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 92
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 92 2 2 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 42 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 92 2 1 21 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 92 (accept_3_2 1 42 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 92)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 92 (allA_succ_of_accept 40 41 92
  (accept_3_2 40 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 92
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 92 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 41 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 92 (accept_3_2 37 41 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 92 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 41 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 92 (Polychromatic418967fa.accept_9_8_5_2_1_422 35
  41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 92 (accept_3_2 34 41 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 92
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 32 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 92 (accept_3_2 31 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  92 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 41 92 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 41 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 92 (accept_3_2 28 41 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 41 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 92 (Polychromatic418967fa.accept_7_5_6_1_1_407 26
  41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 92 (accept_3_2 25 41 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 92 (Polychromatic418967fa.accept_9_6_5_2_1_421 24
  41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 92
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 92 (accept_3_2 22 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 92 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 41 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 92 (accept_3_2 19 41 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 92 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 41 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 92 (Polychromatic418967fa.accept_9_8_5_2_1_422 17
  41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 92 (accept_3_2 16 41 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 92
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 92 (accept_3_2 13 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  92 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 41 92 (Polychromatic418967fa.accept_20_11_1_12_1_3803 11 41 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 92 (accept_3_2 10 41 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 41 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 92 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 92 (accept_3_2 7 41 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 92 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 92
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 92 (accept_3_2 4 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 92
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 92 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 41 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 92 (accept_3_2 1 41 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 92))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 92 (allA_of_3_0 40 40 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 39 92 (allA_succ_of_accept 38 39 92
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 92 (accept_3_2 37 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39
  92 (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 92 (accept_3_2 34 39 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 92 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 39 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 92
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 92 (accept_3_2 31 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39
  92 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 92 (accept_3_2 28 39 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 92 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 39 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 92 (Polychromatic418967fa.accept_7_5_4_1_1_412 26
  39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 92 (accept_3_2 25 39 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 92 (Polychromatic418967fa.accept_7_3_4_1_1_71 24
  39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 92 (accept_3_2 22 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39
  92 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 92 (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 39 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 92 (accept_3_2 19 39 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 92 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 17
  39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 92 (accept_3_2 16 39 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 92 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 92
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 92 (accept_3_2 13 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39
  92 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 92 (accept_3_2 10 39 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 92 (Polychromatic418967fa.accept_17_9_5_7_1_3802 9 39 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 92 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 39
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 92 (accept_3_2 7 39 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 92 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 39
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 39 92 (accept_3_2 4 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 92
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 39 92 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 39 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 92 (accept_3_2 1 39 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 39 92))))))))))))))))))))))))))))))))))))))) (allB_succ 38 92 (allA_succ_of_accept 37 38 92
  (accept_3_2 37 38 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38 92 2 18 19 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 38 92
  (Polychromatic418967fa.accept_10_5_8_2_1_517 35 38 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 38 92 2 17 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 38 92 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 38 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 92 2 16 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 92 (accept_3_2 31 38 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 38 92 2 15 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 38 92 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 38 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 38 92 2 14 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 38 92 (Polychromatic418967fa.accept_43_27_38_6_1_3801
  27 38 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 92 2 13 19 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 92 (accept_3_2 25 38
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 92 2 12 19 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 92
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 38 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 38 92 2 11 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 38 92 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 38 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 92 2 10 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 92 (accept_3_2 19 38 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 38 92 2 9 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 38 92 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 38 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 92 2 8 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 92 (Polychromatic418967fa.accept_10_5_8_2_1_517 15
  38 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 92 2 7 19 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 92 (accept_3_2 13 38
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 92 2 6 19 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 92
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 38 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 92 2 5 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 92 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 38 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 92 2 4 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 92 (accept_3_2 7 38 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 92 2 3 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 92 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 38 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 92 2 2 19 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 92 (Polychromatic418967fa.accept_17_3_4_7_1_1658 3
  38 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 92 2 1 19 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 92 (accept_3_2 1 38
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 92)))))))))))))))))))))))))))))))))))))) (allB_succ 37 92
  (allA_of_3_0 37 37 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 92 (allA_succ_of_accept 35 36 92
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 36 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 92 2 17 18 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 92 (Polychromatic418967fa.accept_16_1_4_12_1_376 33 36 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 92 4 8 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 92 (accept_3_2 31 36 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 36 92 2 15 18 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 36 92 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 36 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 92 4 7 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 92 (Polychromatic418967fa.accept_15_12_6_2_1_2760
  27 36 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 92 2 13 18 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 92 (accept_3_2 25 36
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 92 4 6 9 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 92
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 36 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 36 92 2 11 18 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 36 92 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 36 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 92 4 5 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 92 (accept_3_2 19 36 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 36 92 2 9 18 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 36 92 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 36 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 92 4 4 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 92 (Polychromatic418967fa.accept_16_15_4_12_1_2731
  15 36 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 92 2 7 18 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 92 (accept_3_2 13 36
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 92 4 3 9 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 92
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 36 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 92 2 5 18 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 36 92 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 36 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 92 4 2 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 92 (accept_3_2 7 36 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 36 92 2 3 18 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 36 92 (Polychromatic418967fa.accept_16_5_4_12_1_3800 5 36 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 92 4 1 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 92 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3
  36 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 92 2 1 18 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 92 (accept_3_2 1 36
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 92)))))))))))))))))))))))))))))))))))) (allB_succ 35 92
  (allA_succ_of_accept 34 35 92 (accept_3_2 34 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 92 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 92 (accept_3_2 31 35 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 92 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 92 (Polychromatic418967fa.accept_14_1_7_8_1_2063
  29 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 92 (accept_3_2 28 35
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 92 (Polychromatic418967fa.accept_6_3_5_2_1_12
  27 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 92
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 92 (accept_3_2 25 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35
  92 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 35 92 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 92 (accept_3_2 22 35 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 35 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 92 (Polychromatic418967fa.accept_11_9_2_4_1_707 20
  35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 92 (accept_3_2 19 35 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 92 (Polychromatic418967fa.accept_10_8_5_2_1_881 18
  35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 92
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 92 (accept_3_2 16 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 92 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 35 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 92 (accept_3_2 13 35 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 92 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 92 (Polychromatic418967fa.accept_13_11_9_1_1_1407
  11 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 92 (accept_3_2 10 35
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 92
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 92 (accept_3_2 7 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 92
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 92 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 35 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 92 (accept_3_2 4 35 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 92 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  35 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 92 (accept_3_2 1 35 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 92))))))))))))))))))))))))))))))))))) (allB_succ 34 92
  (allA_of_3_0 34 34 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 92 (allA_succ_of_accept 32 33 92
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 92 (accept_3_2 31 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33
  92 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 92 (accept_3_2 28 33 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 92 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 92 (Polychromatic418967fa.accept_9_8_6_2_1_744 26
  33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 92 (accept_3_2 25 33 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 92 (Polychromatic418967fa.accept_7_3_5_1_1_72 24
  33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 92 (accept_3_2 22 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33
  92 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 92 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 33 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 92 (accept_3_2 19 33 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 92 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 17
  33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 92 (accept_3_2 16 33 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 92 (Polychromatic418967fa.accept_10_5_3_2_1_899 15
  33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 92
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 92 (accept_3_2 13 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33
  92 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 92 (accept_3_2 10 33 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 92 (Polychromatic418967fa.accept_19_9_14_16_1_3791 9 33 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 92 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 33
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 92 (accept_3_2 7 33 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 92 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 33
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 92 (accept_3_2 4 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 92
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 92 (Polychromatic418967fa.accept_16_2_1_12_1_3798 2 33 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 92 (accept_3_2 1 33 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 92))))))))))))))))))))))))))))))))) (allB_succ 32 92 (allA_succ_of_accept 31 32 92
  (accept_3_2 31 32 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 92 2 15 16 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 92
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 32 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 92 4 7 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 92 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 32 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 92 2 13 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 92 (accept_3_2 25 32 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 32 92 4 6 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 32 92 (Polychromatic418967fa.accept_26_23_6_14_1_3796 23 32 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 92 2 11 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 92 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 32
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 92 4 5 8 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 92 (accept_3_2 19 32
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 92 2 9 16 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32 92
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 32 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 32 92 4 4 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 32 92 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 32 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 92 2 7 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 92 (accept_3_2 13 32 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 32 92 4 3 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 32 92 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 32 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 92 2 5 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 92 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9
  32 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 92 4 2 8 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 92 (accept_3_2 7 32
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 92 2 3 16 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 92
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 32 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 92 4 1 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 92 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 32 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 92 2 1 16 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 92 (accept_3_2 1 32 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 92)))))))))))))))))))))))))))))))) (allB_succ 31 92 (allA_of_3_0 31 31 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 30 92 (allA_succ_of_accept 29 30 92 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 30
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 92 2 14 15 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 92
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 30 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 30 92 2 13 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 92 (accept_3_2 25 30 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 92
  2 12 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30
  92 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 92 2 11 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 30 92 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 92 2 10 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 92 (accept_3_2 19 30 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 30 92 2 9 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 30 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 30 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 92 2 8 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 92 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  30 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 92 2 7 15 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 92 (accept_3_2 13 30
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 92 2 6 15 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 92
  (Polychromatic418967fa.accept_17_11_13_7_1_3795 11 30 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 92 2 5 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 92 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 92 2 4 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 92 (accept_3_2 7 30 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 92 2 3 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 30 92 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 30 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 92 2 2 15 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 30
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 92 2 1 15 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 92 (accept_3_2 1 30
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 92)))))))))))))))))))))))))))))) (allB_succ 29 92
  (allA_succ_of_accept 28 29 92 (accept_3_2 28 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 92 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 29 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 92 (accept_3_2 25 29 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 92 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 29 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 92 (Polychromatic418967fa.accept_14_9_1_8_1_2849
  23 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 92 (accept_3_2 22 29
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 92 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 92
  (Polychromatic418967fa.accept_13_7_3_1_1_814 20 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 92 (accept_3_2 19 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29
  92 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 29 92 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 29 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 92 (accept_3_2 16 29 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 29 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 92 (Polychromatic418967fa.accept_11_3_7_4_1_1133
  14 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 92 (accept_3_2 13 29
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 92
  (Polychromatic418967fa.accept_15_12_14_2_1_3794 12 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 29 92 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 29 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 92 (accept_3_2 10 29 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 29 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 92 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8
  29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 92 (accept_3_2 7 29 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 92 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6
  29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 92
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 92 (accept_3_2 4 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 92
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 92 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 29 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 92 (accept_3_2 1 29 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 92))))))))))))))))))))))))))))) (allB_succ 28 92 (allA_of_3_0 28 28 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 92 (allA_succ_of_accept 26 27 92 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 27
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 92 (accept_3_2 25 27 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 92 (Polychromatic418967fa.accept_10_4_7_2_1_211 24
  27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 92 (accept_3_2 22 27 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27
  92 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 92 (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 27 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 92 (accept_3_2 19 27 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 92 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 27 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 17
  27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 92 (accept_3_2 16 27 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 92 (Polychromatic418967fa.accept_8_7_3_4_1_404 15
  27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 92
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 92 (accept_3_2 13 27 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27
  92 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 92 (accept_3_2 10 27 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 92 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 92 (Polychromatic418967fa.accept_16_8_11_12_1_962 8
  27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 92 (accept_3_2 7 27 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 92 (Polychromatic418967fa.accept_12_6_3_8_1_512 6
  27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 92 (accept_3_2 4 27 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 92
  (Polychromatic418967fa.accept_15_3_12_2_1_507 3 27 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 92 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 27 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 92 (accept_3_2 1 27 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 92))))))))))))))))))))))))))) (allB_succ 26 92 (allA_succ_of_accept 25 26 92 (accept_3_2 25
  26 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 92 2 12 13 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 92
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 26 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 92 2 11 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 26 92 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 26 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 92 2 10 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 92 (accept_3_2 19 26 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 26 92 2 9 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 26 92 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 26 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 92 2 8 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 92 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  26 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 92 2 7 13 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 92 (accept_3_2 13 26
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 92 2 6 13 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 92
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 26 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 26 92 2 5 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 26 92 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 26 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 92 2 4 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 92 (accept_3_2 7 26 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 26 92 2 3 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 26 92 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 92 2 2 13 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 92 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 26
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 92 2 1 13 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 92 (accept_3_2 1 26
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 92)))))))))))))))))))))))))) (allB_succ 25 92 (allA_of_3_0 25
  25 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 92 (allA_succ_of_accept 23 24 92
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 92 2 11 12 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 24 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 92 4 5 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 92 (accept_3_2 19 24 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 24 92 2 9 12 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 24 92 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 92 4 4 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 92 (Polychromatic418967fa.accept_16_15_8_12_1_2737
  15 24 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 92 2 7 12 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 92 (accept_3_2 13 24
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 92 4 3 6 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 92
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 24 92 2 5 12 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 24 92 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 92 4 2 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 92 (accept_3_2 7 24 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 24 92 2 3 12 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 24 92 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 92 4 1 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 92 2 1 12 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 92 (accept_3_2 1 24
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 92)))))))))))))))))))))))) (allB_succ 23 92
  (allA_succ_of_accept 22 23 92 (accept_3_2 22 23 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23
  92 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 92 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 23 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 92 (accept_3_2 19 23 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 92 (Polychromatic418967fa.accept_16_2_7_12_1_3793 18 23 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  23 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 92 (accept_3_2 16 23 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  23 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 92
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 92 (accept_3_2 13 23 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  92 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 23 92 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 23 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 92 (accept_3_2 10 23 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 23 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 92 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 92 (accept_3_2 7 23 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 92 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 23
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 92
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 23 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 92 (accept_3_2 4 23 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 92
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 92 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 23 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 92 (accept_3_2 1 23 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 92))))))))))))))))))))))) (allB_succ 22 92 (allA_of_3_0 22 22 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 21 92 (allA_succ_of_accept 20 21 92 (Polychromatic418967fa.accept_13_7_8_1_1_2145 20 21 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 92 (accept_3_2 19 21 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 92 (Polychromatic418967fa.accept_12_6_9_8_1_165 18
  21 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 92 (accept_3_2 16 21 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21
  92 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 92 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 21 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 92 (accept_3_2 13 21 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 92 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 21 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  21 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 92 (accept_3_2 10 21 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 92 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 92
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 21 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 92 (accept_3_2 7 21 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 92
  (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 92 (accept_3_2 4 21 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 92 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 21 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 92 (Polychromatic418967fa.accept_22_2_21_4_1_3792 2
  21 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 92 (accept_3_2 1 21 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 92))))))))))))))))))))) (allB_succ 20 92 (allA_succ_of_accept 19
  20 92 (accept_3_2 19 20 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 92 2 9 10 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 92
  (Polychromatic418967fa.accept_16_1_4_12_1_376 17 20 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 92 4 4 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 92 (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 20 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 92 2 7 10 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 92 (accept_3_2 13 20 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 92 4 3 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 92 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 20 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 92 2 5 10 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 92 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 20
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 92 4 2 5 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 92 (accept_3_2 7 20 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 92 2 3 10 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 92 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 20 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 20 92 4 1 5 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 20 92
  (Polychromatic418967fa.accept_13_3_7_1_1_334 3 20 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 20 92 2 1 10 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 20 92 (accept_3_2 1 20 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  92)))))))))))))))))))) (allB_succ 19 92 (allA_of_3_0 19 19 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 18
  92 (allA_succ_of_accept 17 18 92 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 92 2 8 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 92 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 18 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 18 92 2 7 9 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 92 (accept_3_2 13 18 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 92 2 6 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 92 (Polychromatic418967fa.accept_14_11_4_8_1_664 11
  18 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 92 2 5 9 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 18 92
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 18 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 18 92 2 4 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 18 92 (accept_3_2 7 18 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 92 2
  3 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 92
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 18 92 2 2 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 18 92 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 18 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 18 92 2 1 9 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 92 (accept_3_2 1 18 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 18 92)))))))))))))))))) (allB_succ 17 92 (allA_succ_of_accept 16 17 92 (accept_3_2 16 17 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  17 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 92
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 92 (accept_3_2 13 17 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 17
  92 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 17 92 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 17 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 92 (accept_3_2 10 17 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 17 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 92 (Polychromatic418967fa.accept_16_8_1_12_1_984 8
  17 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 92 (accept_3_2 7 17 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 92 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 17
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 92
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 92 (accept_3_2 4 17 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 92
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 92 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 17 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 92 (accept_3_2 1 17 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 92))))))))))))))))) (allB_succ 16 92 (allA_of_3_0 16 16 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 15 92 (allA_succ_of_accept 14 15 92 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 15 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 92 (accept_3_2 13 15 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 12
  15 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 92
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 92 (accept_3_2 10 15 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15
  92 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 15 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 92 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 15 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 92 (accept_3_2 7 15 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 92 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 15 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 92 (accept_3_2 4 15 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 92 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 15
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 92
  (Polychromatic418967fa.accept_14_2_1_8_1_650 2 15 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 92 (accept_3_2 1 15 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  92))))))))))))))) (allB_succ 14 92 (allA_succ_of_accept 13 14 92 (accept_3_2 13 14 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 14 92 2 6 7 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 14 92 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 14 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 92 2 5 7 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 92 (Polychromatic418967fa.accept_19_9_14_16_1_3791 9
  14 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 92 2 4 7 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 92 (accept_3_2 7 14
  92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 92 2 3 7 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 92 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 92 2 2 7 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 92
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 14 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 14 92 2 1 7 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 14 92 (accept_3_2 1 14 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  92)))))))))))))) (allB_succ 13 92 (allA_of_3_0 13 13 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 92
  (allA_succ_of_accept 11 12 92 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 92 2 5 6 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 92 (Polychromatic418967fa.accept_19_9_12_16_1_3790 9 12 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 92 4 2 3 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 92 (accept_3_2 7 12 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 92 2 3 6 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 92 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 92 4 1 3 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 92
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 12 92 2 1 6 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 92 (accept_3_2 1 12 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 92))))))))))))
  (allB_succ 11 92 (allA_succ_of_accept 10 11 92 (accept_3_2 10 11 92 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 11 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 92 (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 11 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 92 (accept_3_2 7 11 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 92 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 11 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 92
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 11 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 11 92 (accept_3_2 4 11 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 92
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 11 92 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 11 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 92 (accept_3_2 1 11 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 11 92))))))))))) (allB_succ 10 92 (allA_of_3_0 10 10 92 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 9 92 (allA_succ_of_accept 8 9 92 (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 9 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 92 (accept_3_2 7 9 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 92 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 92 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 92 (accept_3_2 4 9 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 92 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 92
  (Polychromatic418967fa.accept_11_2_9_4_1_310 2 9 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 92 (accept_3_2 1 9 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 92)))))))))
  (allB_succ 8 92 (allA_succ_of_accept 7 8 92 (accept_3_2 7 8 92 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 92 2 3 4 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 92 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 92 4 1 2 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 8 92 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 8 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 92 2 1 4 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 92 (accept_3_2 1 8 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 92)))))))) (allB_succ 7 92 (allA_of_3_0 7 7 92 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 92 (allA_succ_of_accept 5 6 92 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 92 2 2 3 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 92 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 6 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 92 2 1 3 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 92 (accept_3_2 1 6 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 92)))))) (allB_succ 5 92 (allA_succ_of_accept 4 5 92 (accept_3_2 4 5 92
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 92 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 92
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 5 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 92 (accept_3_2 1 5 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 92))))) (allB_succ
  4 92 (allA_of_3_0 4 4 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 92 (allA_succ_of_accept 2 3 92
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 3 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 92 (accept_3_2 1 3 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 92))) (allB_succ 2
  92 (allA_succ_of_accept 1 2 92 (accept_3_2 1 2 92 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 92)) (allB_two
  92))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


