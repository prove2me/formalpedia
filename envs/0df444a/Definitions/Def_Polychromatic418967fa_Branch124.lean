-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch124
-- name    : Polychromatic418967fa_Branch124
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:12:08.648178+00:00
-- url     : https://prove2.me/theorems/e6af60c6-bdd6-4288-9cba-2dcac1710c55
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

def Polychromatic418967fa.branch_124 : allB 124 124 :=
  allB_succ' 2 123 124 (Eq.refl Bool.true) (allA_succ_of_accept 1 123 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  123 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 124)) (allB_succ' 3 122 124
  (Eq.refl Bool.true) (allA_of_3_1 3 122 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 121 124 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 121 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 121 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 124 (accept_3_3 2 121 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 121 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 124)))) (allB_succ' 5 120 124 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 120 124 4 1 30 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 120 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 124 2 1 60 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 124))))) (allB_succ' 6 119 124 (Eq.refl
  Bool.true) (allA_of_3_1 6 119 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 118 124 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 118 124 2 3 59 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 124 (accept_3_3 5 118 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  124 2 2 59 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 118 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 124 2 1 59 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 118 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 118 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 124))))))) (allB_succ' 8 117 124 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 117 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 117 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 124 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 117 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 124 (accept_3_3 5 117 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 124 (Polychromatic418967fa.accept_11_4_7_3_1_289 4
  117 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 124
  (Polychromatic418967fa.accept_10_3_7_4_1_584 3 117 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 124 (accept_3_3 2 117 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117 124)))))))) (allB_succ' 9 116 124 (Eq.refl Bool.true) (allA_of_3_1 9 116 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 115 124 (Eq.refl Bool.true) (allA_succ_of_accept 9 115 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 124 (accept_3_3 8 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 124 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 124 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 115 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 124 (accept_3_3 5 115 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 124 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 115 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 124 (accept_3_3 2 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 124)))))))))) (allB_succ' 11 114 124 (Eq.refl Bool.true) (allA_succ_of_gcd 10 114 124 2 5 57
  62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 124
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 114 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 124 2 4 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 124 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 114 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 124 2 3 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 124 (accept_3_3 5 114 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 124 2 2 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 114 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 124 2 1 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  114 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 124))))))))))) (allB_succ' 12 113
  124 (Eq.refl Bool.true) (allA_of_3_1 12 113 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 112 124
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 112 124 4 3 28 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 112 124 (accept_3_3 11 112 124 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 112 124 2 5 56 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 112 124 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 112 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 124 4 2 28 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 112 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 124 2 3 56 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 124 (accept_3_3 5 112 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112 124 4 1 28 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 112 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 3
  112 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 124 2 1 56 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 124
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 112 124))))))))))))) (allB_succ' 14 111 124 (Eq.refl Bool.true) (allA_succ_of_accept 13 111 124
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 111 124 (Polychromatic418967fa.accept_17_12_9_5_1_799 12 111 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 124 (accept_3_3 11 111 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 111 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 111 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 124 (Polychromatic418967fa.accept_15_9_6_4_1_1220
  9 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 124 (accept_3_3 8
  111 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 124
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 111 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 111 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 124 (accept_3_3 5 111 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 111 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 111 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 3
  111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 124 (accept_3_3 2 111
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 124 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 124)))))))))))))) (allB_succ' 15
  110 124 (Eq.refl Bool.true) (allA_of_3_1 15 110 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 109 124
  (Eq.refl Bool.true) (allA_succ_of_accept 15 109 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 109 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 124 (accept_3_3 14 109 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 109 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 109 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 124 (accept_3_3 11 109 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 109 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 124 (accept_3_3 8 109 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 124 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 109 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 124
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 109 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 124 (accept_3_3 5 109 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 109 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 124 (accept_3_3 2 109 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 109 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 124)))))))))))))))) (allB_succ' 17 108 124 (Eq.refl
  Bool.true) (allA_succ_of_gcd 16 108 124 4 4 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 108 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 124 2 7 54 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 124
  (Polychromatic418967fa.accept_23_13_16_9_1_6037 13 108 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 108 124 4 3 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 108 124 (accept_3_3 11 108 124 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 124 2 5 54 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 108 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 124 4 2 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 124 (Polychromatic418967fa.accept_15_7_3_4_1_574 7 108 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 124 2 3 54 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 124 (accept_3_3 5 108 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 124 4 1 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 124 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3
  108 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 124 2 1 54 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 124
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 108 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 124))))))))))))))))) (allB_succ' 18 107 124 (Eq.refl Bool.true) (allA_of_3_1 18 107 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 106 124 (Eq.refl Bool.true) (allA_succ_of_gcd 18 106 124 2 9 53 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 106 124
  (accept_3_3 17 106 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 106 124 2 8 53 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 106 124
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 106 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 106 124 2 7 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 106 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 106 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 124 2 6 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 124 (accept_3_3 11 106 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 124 2 5 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 124 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 106 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 124 2 4 53 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 124
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 106 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 124 2 3 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 124 (accept_3_3 5 106 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  124 2 2 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 106 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 124 2 1 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 106 124 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 106 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 124))))))))))))))))))) (allB_succ' 20 105 124 (Eq.refl
  Bool.true) (allA_succ_of_accept 19 105 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 105 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 124 (Polychromatic418967fa.accept_12_6_9_4_1_96
  18 105 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 124 (accept_3_3 17
  105 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 124
  (Polychromatic418967fa.accept_10_6_5_4_1_571 16 105 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 105 124 (Polychromatic418967fa.accept_20_15_5_4_1_4566 15 105 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 124 (accept_3_3 14 105 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 105 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 124 (Polychromatic418967fa.accept_9_3_6_7_1_562
  12 105 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 124 (accept_3_3 11
  105 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 124
  (Polychromatic418967fa.accept_9_1_6_7_1_285 10 105 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 105 124 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 105 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 124 (accept_3_3 8 105 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 105 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 105 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 124 (Polychromatic418967fa.accept_10_6_5_4_1_571 6
  105 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 124 (accept_3_3 5 105
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 124
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 105 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 105 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 105 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 124 (accept_3_3 2 105 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 105 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 124)))))))))))))))))))) (allB_succ' 21 104 124 (Eq.refl
  Bool.true) (allA_of_3_1 21 104 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 103 124 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 103 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 103 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 124 (accept_3_3 20 103 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 103 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 103 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 124 (Polychromatic418967fa.accept_11_7_4_3_1_302
  18 103 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 124 (accept_3_3 17
  103 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 124
  (Polychromatic418967fa.accept_17_16_1_5_1_2600 16 103 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 103 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 124 (accept_3_3 14 103 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 103 124 (Polychromatic418967fa.accept_20_13_3_4_1_6036 13 103 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 124
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 124 (accept_3_3 11 103 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 103 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 103 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 124 (accept_3_3 8 103 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 124 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 103 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 124
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 103 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 124 (accept_3_3 5 103 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 124 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 103 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 124 (accept_3_3 2 103 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 103 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 124)))))))))))))))))))))) (allB_succ' 23 102 124
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 102 124 2 11 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 124 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 102 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 124 2 10 51 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 124
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 102 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 124 2 9 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 124 (accept_3_3 17 102 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  102 124 2 8 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 102 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 102 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 102 124 2 7 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 102 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 102 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 124 2 6 51 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 124 (accept_3_3 11 102 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 124 2 5 51 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 124
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 102 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 124 2 4 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 102 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 124 2 3 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 124 (accept_3_3 5 102 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 124 2 2 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 124 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 102 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 124 2 1 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 1
  102 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 124)))))))))))))))))))))))
  (allB_succ' 24 101 124 (Eq.refl Bool.true) (allA_of_3_1 24 101 124 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 25 100 124 (Eq.refl Bool.true) (allA_succ_of_gcd 24 100 124 4 6 25 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 124 (accept_3_3 23 100 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 124 2 11 50 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 21
  100 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 124 4 5 25 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 124
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 100 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 100 124 2 9 50 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 100 124 (accept_3_3 17 100 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  100 124 4 4 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 100 124 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 100 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 100 124 2 7 50 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 100 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 100 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 124 4 3 25 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 124 (accept_3_3 11 100 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 124 2 5 50 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 124
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 100 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 124 4 2 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 124 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 100 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 124 2 3 50 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 124 (accept_3_3 5 100 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 100 124 4 1 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 100 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 100 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 124 2 1 50 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 124 (Polychromatic418967fa.accept_16_1_4_12_1_376 1
  100 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 124)))))))))))))))))))))))))
  (allB_succ' 26 99 124 (Eq.refl Bool.true) (allA_succ_of_accept 25 99 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25
  99 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 124
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 124 (accept_3_3 23 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  99 124 (Polychromatic418967fa.accept_13_9_8_7_1_1073 22 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 99 124 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 99 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 124 (accept_3_3 20 99 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 124
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 99 124 (accept_3_3 17 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  99 124 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 99 124 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 124 (accept_3_3 14 99 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 99 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 124
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 124 (accept_3_3 11 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 124 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 99 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 124 (accept_3_3 8 99 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 124
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 124 (accept_3_3 5 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  124 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 99 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 99 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 124 (accept_3_3 2 99 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 99 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 99 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 124)))))))))))))))))))))))))) (allB_succ' 27 98 124 (Eq.refl
  Bool.true) (allA_of_3_1 27 98 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 97 124 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 97 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 97 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 124 (accept_3_3 26 97 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 97 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 97 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 124 (Polychromatic418967fa.accept_16_8_1_12_1_984
  24 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 124 (accept_3_3 23
  97 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 124
  (Polychromatic418967fa.accept_7_1_6_5_1_39 22 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 97 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 124 (accept_3_3 20 97 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 97 124 (Polychromatic418967fa.accept_18_1_7_16_1_1342 19 97 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 124
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 124 (accept_3_3 17 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 124 (Polychromatic418967fa.accept_21_16_13_19_1_6035 16 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 97 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 124 (accept_3_3 14 97 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 124 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 97 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 124
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 124 (accept_3_3 11 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 124 (accept_3_3 8 97 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 124 (Polychromatic418967fa.accept_17_7_12_5_1_1580 7 97 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 124
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 124 (accept_3_3 5 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  124 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 97 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 124 (accept_3_3 2 97 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 124)))))))))))))))))))))))))))) (allB_succ' 29 96 124 (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 96 124 4 7 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 124 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 96 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 124 2 13 48 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 124
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 96 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 124 4 6 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 124 (accept_3_3 23 96 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96
  124 2 11 48 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  96 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 124 4 5 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 124 2 9 48 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 124 (accept_3_3 17 96 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 124 4 4 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 96 124 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 96 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 124 2 7 48 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 124
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 124 4 3 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 124 (accept_3_3 11 96 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  124 2 5 48 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 124 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 96 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 124 4 2 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 124 (Polychromatic418967fa.accept_17_7_11_5_1_3539 7 96 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 124 2 3 48 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 124 (accept_3_3 5 96 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 124 4 1 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 124 2 1 48 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 124
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 96 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 124))))))))))))))))))))))))))))) (allB_succ' 30 95 124 (Eq.refl Bool.true) (allA_of_3_1 30 95 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 94 124 (Eq.refl Bool.true) (allA_succ_of_gcd 30 94 124 2 15 47
  62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 94 124
  (accept_3_3 29 94 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94 124 2 14 47 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 94 124
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 94 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 94 124 2 13 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 94 124 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 94 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 124 2 12 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 124 (accept_3_3 23 94 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 124 2 11 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 94 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 124 2 10 47 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 124
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 94 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 124 2 9 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 124 (accept_3_3 17 94 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  124 2 8 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 94 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 124 2 7 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 94 124 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 94 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 124 2 6 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 124 (accept_3_3 11 94 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 124 2 5 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 94 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 94 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 94 124 2 4 47 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 94 124
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 94 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 94 124 2 3 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 94 124 (accept_3_3 5 94 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 124
  2 2 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94
  124 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 94 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 94 124 2 1 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 94 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 94 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 94 124))))))))))))))))))))))))))))))) (allB_succ' 32 93 124 (Eq.refl
  Bool.true) (allA_succ_of_gcd 31 93 124 31 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 30 93 124 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 93 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 124 (accept_3_3 29 93 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 93 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 124
  (Polychromatic418967fa.accept_10_7_3_4_1_978 27 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 124 (accept_3_3 26 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 124 (accept_3_3 23 93 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 93 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 124
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 124 (accept_3_3 20 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 93 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 124 (accept_3_3 17 93 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 124 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 93 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 124
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 124 (accept_3_3 14 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 124 (Polychromatic418967fa.accept_17_12_8_5_1_6018 12 93 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 124 (accept_3_3 11 93 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 93 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 124
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 124 (accept_3_3 8 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 93 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 124 (accept_3_3 5 93 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 93 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  93 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 124 (accept_3_3 2 93 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 124))))))))))))))))))))))))))))))))
  (allB_succ' 33 92 124 (Eq.refl Bool.true) (allA_of_3_1 33 92 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  34 91 124 (Eq.refl Bool.true) (allA_succ_of_accept 33 91 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 91 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 124 (accept_3_3 32 91 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 124 (Polychromatic418967fa.accept_8_7_3_4_1_404 31
  91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 124 (accept_3_3 29 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 124 (Polychromatic418967fa.accept_17_11_6_5_1_3662 28 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 124 (accept_3_3 26 91 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 124 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 91 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 124
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 124 (accept_3_3 23 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 91 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 124 (accept_3_3 20 91 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 124 (Polychromatic418967fa.accept_14_5_7_12_1_4006 19 91 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 124
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 124 (accept_3_3 17 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 124 (Polychromatic418967fa.accept_14_2_7_12_1_1485 16 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 124 (accept_3_3 14 91 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 91 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 124 (accept_3_3 11 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 124 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 124 (accept_3_3 8 91 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 124 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 91 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 124
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 124 (accept_3_3 5 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  124 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 124 (accept_3_3 2 91 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 124 (Polychromatic418967fa.accept_16_1_11_12_1_1774 1 91 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 124)))))))))))))))))))))))))))))))))) (allB_succ' 35 90 124
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 90 124 2 17 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 90 124 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 90 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 124 2 16 45 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 124
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 90 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 124 2 15 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 124 (accept_3_3 29 90 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90
  124 2 14 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  90 124 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 90 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 90 124 2 13 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 90 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 90 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 124 2 12 45 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 124 (accept_3_3 23 90 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 124 2 11 45 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 124
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 90 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 124 2 10 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 124 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 90 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 124 2 9 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 124 (accept_3_3 17 90 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 90 124 2 8 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 90 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 90 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 124 2 7 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 124 (Polychromatic418967fa.accept_14_13_6_12_1_3126
  13 90 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 124 2 6 45 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 124 (accept_3_3 11
  90 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 124 2 5 45 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 124
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 90 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 124 2 4 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 124 (Polychromatic418967fa.accept_19_7_14_10_1_6034 7 90 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 124 2 3 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 124 (accept_3_3 5 90 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 90 124 2 2 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 124 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 90 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 124 2 1 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 90
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 124)))))))))))))))))))))))))))))))))))
  (allB_succ' 36 89 124 (Eq.refl Bool.true) (allA_of_3_1 36 89 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  37 88 124 (Eq.refl Bool.true) (allA_succ_of_gcd 36 88 124 4 9 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 88 124 (accept_3_3 35 88 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 88 124 2 17 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 88 124 (Polychromatic418967fa.accept_16_1_8_12_1_405 33 88 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 88 124 4 8 22 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 88 124
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 31 88 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 88 124 2 15 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 88 124 (accept_3_3 29 88 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88
  124 4 7 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  88 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 88 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 88 124 2 13 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 88 124 (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 88 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 124 4 6 22 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 124 (accept_3_3 23 88 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 124 2 11 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 124 (Polychromatic418967fa.accept_13_8_10_7_1_1702
  21 88 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 124 4 5 22 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 124
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 88 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 124 2 9 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 124 (accept_3_3 17 88 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  124 4 4 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 88 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 124 2 7 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 88 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 124 4 3 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 124 (accept_3_3 11 88 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 124 2 5 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 88 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 124 4 2 22 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 124
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 7 88 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 124 2 3 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 124 (accept_3_3 5 88 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 124
  4 1 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  124 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 88 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 88 124 2 1 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 88 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 88 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 124))))))))))))))))))))))))))))))))))))) (allB_succ' 38 87 124
  (Eq.refl Bool.true) (allA_succ_of_accept 37 87 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 87 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 124
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 124 (accept_3_3 35 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  87 124 (Polychromatic418967fa.accept_13_8_9_7_1_530 34 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 124 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 124 (accept_3_3 32 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 124
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 87 124 (accept_3_3 29 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  87 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 87 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 124 (accept_3_3 26 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 87 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 124
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 87 124 (accept_3_3 23 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  87 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 87 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 124 (accept_3_3 20 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 124
  (Polychromatic418967fa.accept_11_7_10_3_1_633 18 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 87 124 (accept_3_3 17 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  87 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 124 (accept_3_3 14 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 124
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 124 (accept_3_3 11 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  87 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 124 (accept_3_3 8 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 124
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 124 (accept_3_3 5 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  124 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 87 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 124 (accept_3_3 2 87 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 124)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 86 124
  (Eq.refl Bool.true) (allA_of_3_1 39 86 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 85 124 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 85 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 124 (accept_3_3 38 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 85 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 124
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 124 (accept_3_3 35 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 124 (accept_3_3 32 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 85 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 124
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 124 (accept_3_3 29 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 124 (accept_3_3 26 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 124 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 85 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 124
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 124 (accept_3_3 23 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 124 (accept_3_3 20 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 85 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 124
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 124 (accept_3_3 17 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 124 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 124 (accept_3_3 14 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 124
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 124 (accept_3_3 11 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 124 (accept_3_3 8 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 124 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 85 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 124
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 124 (accept_3_3 5 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  124 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 85 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 124 (accept_3_3 2 85 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 124 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 85 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 124)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 84
  124 (Eq.refl Bool.true) (allA_succ_of_gcd 40 84 124 4 10 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 124 (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 84 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 124 2 19 42 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 124
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 124 4 9 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 124 (accept_3_3 35 84 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84
  124 2 17 42 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  84 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 84 124 4 8 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 84 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 124 2 15 42 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 124 (accept_3_3 29 84 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 124 4 7 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 124 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 84 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 124 2 13 42 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 124
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 84 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 124 4 6 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 124 (accept_3_3 23 84 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84
  124 2 11 42 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  84 124 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 84 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 84 124 4 5 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 84 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 124 2 9 42 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 124 (accept_3_3 17 84 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 124 4 4 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 84 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 124 2 7 42 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 124
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 124 4 3 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 124 (accept_3_3 11 84 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84
  124 2 5 42 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  84 124 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 84 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 84 124 4 2 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 84 124 (Polychromatic418967fa.accept_16_7_4_12_1_1806 7 84 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 124 2 3 42 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 124 (accept_3_3 5 84 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 124 4 1 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 84 124 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 84 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 124 2 1 42 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 124
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 124))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 83 124 (Eq.refl Bool.true) (allA_of_3_1 42 83
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 82 124 (Eq.refl Bool.true) (allA_succ_of_gcd 42 82 124 2
  21 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82
  124 (accept_3_3 41 82 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 124 2 20 41 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 82 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 82 124 2 19 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 82 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 37 82 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 124 2 18 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 124 (accept_3_3 35 82 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 124 2 17 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 124 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 82 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 124 2 16 41 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 124
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 82 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 124 2 15 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 82 124 (accept_3_3 29 82 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82
  124 2 14 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  82 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 82 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 82 124 2 13 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 82 124 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 82 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 124 2 12 41 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 124 (accept_3_3 23 82 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 124 2 11 41 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 82 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 82 124 2 10 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 82 124 (Polychromatic418967fa.accept_11_8_5_3_1_694 19 82 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 124 2 9 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 124 (accept_3_3 17 82 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 82 124 2 8 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 82 124 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 82 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 124 2 7 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  82 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 124 2 6 41 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 124 (accept_3_3 11
  82 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 124 2 5 41 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 124
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 82 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 124 2 4 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 82 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 124 2 3 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 124 (accept_3_3 5 82 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 124 2 2 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 82 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 124 2 1 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 124 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  82 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  124))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 81 124 (Eq.refl Bool.true) (allA_succ_of_accept 43 81
  124 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 81 124 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 81 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 124 (accept_3_3 41 81 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 81 124 (Polychromatic418967fa.accept_11_7_4_3_1_302 40 81 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 124 (Polychromatic418967fa.accept_15_9_6_4_1_1220
  39 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 124 (accept_3_3 38
  81 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 124
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 81 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 124 (accept_3_3 35 81 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 81 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 81 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 124
  (Polychromatic418967fa.accept_18_15_9_16_1_6029 33 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 124 (accept_3_3 32 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 81 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 124 (accept_3_3 29 81 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 124 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 81 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 124
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 124 (accept_3_3 26 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 124 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 81 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 124 (accept_3_3 23 81 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 81 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 124
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 124 (accept_3_3 20 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 124 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 81 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 124 (accept_3_3 17 81 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 81 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 124
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 124 (accept_3_3 14 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 124 (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 81 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 124 (accept_3_3 11 81 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 124 (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 81
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 124
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 124 (accept_3_3 8 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 124 (accept_3_3 5 81 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 124 (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 81 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 124 (Polychromatic418967fa.accept_19_3_5_10_1_6033
  3 81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 124 (accept_3_3 2 81
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  81 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  124)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 80 124 (Eq.refl Bool.true) (allA_of_3_1 45 80 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 79 124 (Eq.refl Bool.true) (allA_succ_of_accept 45 79 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 124 (accept_3_3 44 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 124 (Polychromatic418967fa.accept_13_3_1_7_1_1706 42 79 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 124 (accept_3_3 41 79 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 124 (Polychromatic418967fa.accept_16_8_15_12_1_1747 40 79 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 124 (accept_3_3 38 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 124 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 124 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 79 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 124 (accept_3_3 35 79 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 124 (Polychromatic418967fa.accept_11_1_2_3_1_688 34 79 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 124 (accept_3_3 32 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 124 (Polychromatic418967fa.accept_19_11_3_10_1_3354 30 79 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 124 (accept_3_3 29 79 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 124 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 79 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 124 (accept_3_3 26 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 124 (accept_3_3 23 79 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 124 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 79 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 124 (accept_3_3 20 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 79 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 124 (accept_3_3 17 79 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 124 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 79 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 124 (accept_3_3 14 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 124 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 124 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 79 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 124 (accept_3_3 11 79 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 79 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 124 (accept_3_3 8 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  124 (Polychromatic418967fa.accept_14_7_9_12_1_3975 7 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 124 (Polychromatic418967fa.accept_13_6_1_7_1_1690 6 79 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 124 (accept_3_3 5 79 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 79 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 124 (accept_3_3 2 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  124 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 79 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 124)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 78 124 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 78 124 2 23 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 78 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 78 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 124 2 22 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 124 (Polychromatic418967fa.accept_19_5_2_10_1_3371
  43 78 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 124 2 21 39 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 124 (accept_3_3 41
  78 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 124 2 20 39 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 124
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 78 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 124 2 19 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 78 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 78 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 124 2 18 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 124 (accept_3_3 35 78 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 124 2 17 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 124 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 78 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 124 2 16 39 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 124
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 78 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 124 2 15 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 124 (accept_3_3 29 78 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78
  124 2 14 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  78 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 78 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 78 124 2 13 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 78 124 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 78 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 124 2 12 39 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 124 (accept_3_3 23 78 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 124 2 11 39 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 124
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 124 2 10 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 78 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 124 2 9 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 124 (accept_3_3 17 78 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 78 124 2 8 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 78 124 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 78 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 124 2 7 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 13
  78 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 124 2 6 39 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 124 (accept_3_3 11
  78 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 124 2 5 39 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 124
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 78 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 124 2 4 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 124 (Polychromatic418967fa.accept_15_7_3_4_1_574 7 78 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 124 2 3 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 124 (accept_3_3 5 78 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 124 2 2 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 78 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 124 2 1 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  124))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 77 124 (Eq.refl Bool.true) (allA_of_3_1 48 77 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 76 124 (Eq.refl Bool.true) (allA_succ_of_gcd 48 76 124 4 12 19
  31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 76 124
  (accept_3_3 47 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76 124 2 23 38 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 76 124
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 76 124 4 11 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 76 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 76 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 124 2 21 38 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 124 (accept_3_3 41 76 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 124 4 10 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 76 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 124 2 19 38 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 124
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 124 4 9 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 76 124 (accept_3_3 35 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76
  124 2 17 38 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  76 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 76 124 4 8 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 76 124 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 76 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 76 124 2 15 38 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 76 124 (accept_3_3 29 76 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76 124 4 7 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 76 124 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 76 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 124 2 13 38 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 124
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 76 124 4 6 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 76 124 (accept_3_3 23 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76
  124 2 11 38 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  76 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 76 124 4 5 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 76 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 124 2 9 38 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 124 (accept_3_3 17 76 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 124 4 4 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 76 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 76 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 124 2 7 38 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 124
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 13 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 76 124 4 3 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 76 124 (accept_3_3 11 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76
  124 2 5 38 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  76 124 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 76 124 4 2 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 76 124 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 76 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 124 2 3 38 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 124 (accept_3_3 5 76 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 124 4 1 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 76 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 76 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 124 2 1 38 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 124
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 76 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 124))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 75 124 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 75 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 75 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 124 (Polychromatic418967fa.accept_21_6_12_19_1_6032 48 75
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 124 (accept_3_3 47 75 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 46
  75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 124
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 45 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 124 (accept_3_3 44 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 124 (accept_3_3 41 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 75 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 124
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 124 (accept_3_3 38 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 124 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 124 (accept_3_3 35 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 124 (Polychromatic418967fa.accept_13_8_10_7_1_1702 34 75 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 124
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 124 (accept_3_3 32 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 124 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 124 (accept_3_3 29 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 75 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 124
  (Polychromatic418967fa.accept_19_8_18_10_1_3360 27 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 124 (accept_3_3 26 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 124 (accept_3_3 23 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 75 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 124
  (Polychromatic418967fa.accept_10_1_5_4_1_276 21 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 124 (accept_3_3 20 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 124 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 124 (accept_3_3 17 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 124 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 75 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 124
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 124 (accept_3_3 14 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 124 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 75 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 124 (accept_3_3 11 75 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 75 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 124
  (Polychromatic418967fa.accept_10_9_5_4_1_966 9 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 124 (accept_3_3 8 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 75 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 124 (accept_3_3 5 75 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 75 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 124 (Polychromatic418967fa.accept_13_3_10_7_1_1061
  3 75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 124 (accept_3_3 2 75
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  75 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  124)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 74 124 (Eq.refl Bool.true) (allA_of_3_1 51 74 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 73 124 (Eq.refl Bool.true) (allA_succ_of_accept 51 73 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 73 124 (accept_3_3 50 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  73 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 73 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 124 (accept_3_3 47 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 73 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 73 124 (accept_3_3 44 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  73 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 73 124 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 124 (accept_3_3 41 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 124 (accept_3_3 38 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 124 (accept_3_3 35 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 73 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 124 (accept_3_3 32 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 124 (accept_3_3 29 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 124 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 73 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 124 (accept_3_3 26 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 124 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 124 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 124 (accept_3_3 23 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 73 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 124 (accept_3_3 20 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 124 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 124 (Polychromatic418967fa.accept_16_2_9_12_1_46 18 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 124 (accept_3_3 17 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 73 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 124 (accept_3_3 14 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 124 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 124 (accept_3_3 11 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 124 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 73 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 124 (accept_3_3 8 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  124 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 73 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 124 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 124 (accept_3_3 5 73 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 124 (accept_3_3 2 73 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  124)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 72 124 (Eq.refl Bool.true) (allA_succ_of_gcd 52
  72 124 4 13 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  51 72 124 (Polychromatic418967fa.accept_16_3_8_12_1_2736 51 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 72 124 2 25 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 72 124 (Polychromatic418967fa.accept_14_7_2_12_1_1430 49 72 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 124 4 12 18 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 124 (accept_3_3 47 72 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 124 2 23 36 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 124
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 124 4 11 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 124 (Polychromatic418967fa.accept_16_11_8_12_1_1767 43 72 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 124 2 21 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 124 (accept_3_3 41 72 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 124 4 10 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 124 2 19 36 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 124
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 124 4 9 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 124 (accept_3_3 35 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72
  124 2 17 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  72 124 (Polychromatic418967fa.accept_16_1_8_12_1_405 33 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 72 124 4 8 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 72 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 72 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 124 2 15 36 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 124 (accept_3_3 29 72 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 124 4 7 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 72 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 124 2 13 36 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 124
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 124 4 6 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 124 (accept_3_3 23 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  124 2 11 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  72 124 (Polychromatic418967fa.accept_14_7_2_12_1_1430 21 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 124 4 5 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 124 (Polychromatic418967fa.accept_11_8_6_3_1_661 19 72 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 124 2 9 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 124 (accept_3_3 17 72 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 124 4 4 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 72 124 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 72 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 124 2 7 36 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 124
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 13 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 124 4 3 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 124 (accept_3_3 11 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72
  124 2 5 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  72 124 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 72 124 4 2 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 72 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 72 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 124 2 3 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 124 (accept_3_3 5 72 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 124 4 1 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 72 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 124 2 1 36 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 124
  (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 72 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 124))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 71 124 (Eq.refl Bool.true)
  (allA_of_3_1 54 71 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 70 124 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 70 124 2 27 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 70 124 (accept_3_3 53 70 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70
  124 2 26 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  70 124 (Polychromatic418967fa.accept_11_7_4_3_1_302 51 70 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 70 124 2 25 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 70 124 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 70 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 124 2 24 35 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 124 (accept_3_3 47 70 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 124 2 23 35 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 124
  (Polychromatic418967fa.accept_20_5_10_4_1_4548 45 70 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 70 124 2 22 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 70 124 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 70 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 124 2 21 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 124 (accept_3_3 41 70 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 124 2 20 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 124 (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 70 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 124 2 19 35 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 124
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 70 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 124 2 18 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 70 124 (accept_3_3 35 70 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70
  124 2 17 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  70 124 (Polychromatic418967fa.accept_17_16_2_5_1_6031 33 70 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 70 124 2 16 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 70 124 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 70 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 124 2 15 35 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 124 (accept_3_3 29 70 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 124 2 14 35 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 124
  (Polychromatic418967fa.accept_37_27_33_13_1_6030 27 70 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 70 124 2 13 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 70 124 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 70 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 124 2 12 35 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 124 (accept_3_3 23 70 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 124 2 11 35 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 124
  (Polychromatic418967fa.accept_15_6_10_4_1_150 21 70 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 124 2 10 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 124 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 70 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 124 2 9 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 124 (accept_3_3 17 70 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 70 124 2 8 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 70 124 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 70 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 124 2 7 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 124 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 70 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 124 2 6 35 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 124 (accept_3_3 11
  70 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 124 2 5 35 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 124
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 70 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 124 2 4 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 124 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 70 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 124 2 3 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 124 (accept_3_3 5 70 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 124 2 2 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 124 (Polychromatic418967fa.accept_17_3_2_5_1_2556 3 70 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 124 2 1 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 124 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  70 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  124))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 69 124 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 69 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 69 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 124 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 69 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 124 (accept_3_3 53 69 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 124 (Polychromatic418967fa.accept_16_4_5_12_1_2749
  52 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 124
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 51 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 124 (accept_3_3 50 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 124 (accept_3_3 47 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 69 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 124
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 124 (accept_3_3 44 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 124 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 124 (accept_3_3 41 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 124 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 69 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 124
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 124 (accept_3_3 38 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 124 (accept_3_3 35 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 124 (Polychromatic418967fa.accept_14_6_13_12_1_810 34 69 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 124
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 124 (accept_3_3 32 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 124 (accept_3_3 29 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 69 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 124
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 124 (accept_3_3 26 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 124 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 69 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 124 (accept_3_3 23 69 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 69 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 124
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 124 (accept_3_3 20 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 124 (accept_3_3 17 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 124 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 69 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 124
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 124 (accept_3_3 14 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 124 (accept_3_3 11 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 69 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 124
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 124 (accept_3_3 8 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 124 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 124 (accept_3_3 5 69 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 69 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  69 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 124 (accept_3_3 2 69 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  124)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 68 124 (Eq.refl Bool.true) (allA_of_3_1 57
  68 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 67 124 (Eq.refl Bool.true) (allA_succ_of_accept 57 67
  124 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 67 124 (accept_3_3 56 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  67 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 67 124 (Polychromatic418967fa.accept_21_12_4_19_1_4526 54 67 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 67 124 (accept_3_3 53 67 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 67 124 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 67 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 67 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 67 124 (accept_3_3 50 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  67 124 (Polychromatic418967fa.accept_21_7_4_19_1_4525 49 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 67 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 67 124 (accept_3_3 47 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 67 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 67 124 (accept_3_3 44 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  67 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 67 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 124 (accept_3_3 41 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 67 124 (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 67 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 67 124 (accept_3_3 38 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 124 (accept_3_3 35 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 67 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 124 (accept_3_3 32 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 124 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 124 (accept_3_3 29 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 124 (accept_3_3 26 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 124 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 124 (accept_3_3 23 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 67 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 124 (accept_3_3 20 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 124 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 124 (accept_3_3 17 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 67 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 124 (accept_3_3 14 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 124 (accept_3_3 11 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 67 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 124 (accept_3_3 8 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  124 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 67 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 67 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 124 (accept_3_3 5 67 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 124 (Polychromatic418967fa.accept_16_4_3_12_1_4892 4 67 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 124 (accept_3_3 2 67 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 67
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  124)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 66 124 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 66 124 2 29 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 66 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 66 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 124 2 28 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 66
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 124 2 27 33 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 124 (accept_3_3 53
  66 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 124 2 26 33 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 124
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 124 2 25 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 66 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 124 2 24 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 124 (accept_3_3 47 66 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 124 2 23 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 124 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 66 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 124 2 22 33 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 124
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 124 2 21 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 124 (accept_3_3 41 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66
  124 2 20 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  66 124 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 66 124 2 19 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 66 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 66 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 124 2 18 33 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 124 (accept_3_3 35 66 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 124 2 17 33 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 124
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 124 2 16 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 66 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 124 2 15 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 124 (accept_3_3 29 66 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 124 2 14 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 124 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 66 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 124 2 13 33 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 124
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 124 2 12 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 124 (accept_3_3 23 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66
  124 2 11 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  66 124 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 66 124 2 10 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 66 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 124 2 9 33 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 124 (accept_3_3 17 66 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 124 2 8 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 66 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 124 2 7 33 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 124
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 124 2 6 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 124 (accept_3_3 11 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66
  124 2 5 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  66 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 66 124 2 4 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 66 124 (Polychromatic418967fa.accept_16_7_2_12_1_1754 7 66 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 124 2 3 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 124 (accept_3_3 5 66 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 124 2 2 33 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 66 124 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 66 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 124 2 1 33 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 124
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 66 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 124))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 65 124 (Eq.refl Bool.true)
  (allA_of_3_1 60 65 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 64 124 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 64 124 4 15 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 64 124 (accept_3_3 59 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64
  124 2 29 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  64 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 64 124 4 14 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 64 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 64 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 124 2 27 32 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 124 (accept_3_3 53 64 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 124 4 13 16 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 124
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 64 124 2 25 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 64 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 64 124 4 12 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 64 124 (accept_3_3 47 64 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64 124 2 23 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 64 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 64 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 64 124 4 11 16 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 64 124
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 43 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 64 124 2 21 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 64 124 (accept_3_3 41 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64
  124 4 10 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  64 124 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 64 124 2 19 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 64 124 (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 64 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 124 4 9 16 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 124 (accept_3_3 35 64 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 124 2 17 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 124 (Polychromatic418967fa.accept_9_6_1_7_1_577 33
  64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 124 4 8 16 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 124
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 124 2 15 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 124 (accept_3_3 29 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  124 4 7 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 124 2 13 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 124 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 64 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 124 4 6 16 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 124 (accept_3_3 23 64 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 124 2 11 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 21
  64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 124 4 5 16 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 124
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 124 2 9 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 124 (accept_3_3 17 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  124 4 4 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 124 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 124 2 7 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 64 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 124 4 3 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 124 (accept_3_3 11 64 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 124 2 5 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 64 124 (Polychromatic418967fa.accept_17_9_13_5_1_3512 9 64 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 124 4 2 16 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 124
  (Polychromatic418967fa.accept_21_7_1_19_1_6021 7 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 124 2 3 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 124 (accept_3_3 5 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 124
  4 1 16 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  124 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 64 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 124 2 1 32 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 124 (Polychromatic418967fa.accept_18_1_10_16_1_566 1 64 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 124)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 63 124 (Eq.refl Bool.true) (allA_succ_of_accept 61 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 61
  63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 63 124
  (Polychromatic418967fa.accept_11_5_8_3_1_66 60 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 63 124 (accept_3_3 59 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  63 124 (Polychromatic418967fa.accept_14_2_7_12_1_1485 58 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 63 124 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 124 (accept_3_3 56 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 124
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 63 124 (accept_3_3 53 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  63 124 (Polychromatic418967fa.accept_15_7_3_4_1_574 52 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 63 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 124 (accept_3_3 50 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 124
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 63 124 (accept_3_3 47 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  63 124 (Polychromatic418967fa.accept_15_1_3_4_1_1217 46 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 63 124 (Polychromatic418967fa.accept_16_13_15_12_1_1748 45 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 124 (accept_3_3 44 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 63 124
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 63 124 (accept_3_3 41 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  63 124 (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 124 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 124 (accept_3_3 38 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 124
  (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 63 124 (accept_3_3 35 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  63 124 (Polychromatic418967fa.accept_16_2_15_12_1_1744 34 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 63 124 (Polychromatic418967fa.accept_14_5_7_12_1_4006 33 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 124 (accept_3_3 32 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 124
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 124 (accept_3_3 29 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  63 124 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 63 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 124 (accept_3_3 26 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 124
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 124 (accept_3_3 23 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  63 124 (Polychromatic418967fa.accept_13_9_11_7_1_1077 22 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 63 124 (Polychromatic418967fa.accept_19_2_6_10_1_3364 21 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 124 (accept_3_3 20 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 124
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 124 (accept_3_3 17 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  63 124 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 124 (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 124 (accept_3_3 14 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 124
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 124 (accept_3_3 11 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  63 124 (Polychromatic418967fa.accept_17_10_12_5_1_6028 10 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 124 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 124 (accept_3_3 8 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 124
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 124 (accept_3_3 5 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  124 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 63 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 124 (accept_3_3 2 63 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  124)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 124 (allA_of_3_1 62 62 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 124 (allA_succ_of_accept 60 61 124
  (Polychromatic418967fa.accept_13_8_9_7_1_530 60 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 124 (accept_3_3 59 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 124 (accept_3_3 56 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 124 (Polychromatic418967fa.accept_10_5_1_4_1_1444 55 61 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 124
  (Polychromatic418967fa.accept_13_2_9_7_1_164 54 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 124 (accept_3_3 53 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 124 (Polychromatic418967fa.accept_11_8_6_3_1_661 52 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 124 (accept_3_3 50 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 124 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 61 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 124
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 48 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 124 (accept_3_3 47 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 124 (accept_3_3 44 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 124 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 61 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 124
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 124 (accept_3_3 41 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 124 (Polychromatic418967fa.accept_16_8_13_12_1_3809 40 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 124 (accept_3_3 38 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 124 (Polychromatic418967fa.accept_10_7_1_4_1_1447 37 61 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 124
  (Polychromatic418967fa.accept_16_4_13_12_1_1740 36 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 124 (accept_3_3 35 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 124 (accept_3_3 32 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 124 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 61 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 124
  (Polychromatic418967fa.accept_11_8_6_3_1_661 30 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 124 (accept_3_3 29 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 124 (Polychromatic418967fa.accept_13_2_9_7_1_164 28 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 124 (accept_3_3 26 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 124 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 61 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 124
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 124 (accept_3_3 23 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 124 (accept_3_3 20 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 124 (Polychromatic418967fa.accept_11_8_6_3_1_661 19 61 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 124
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 124 (accept_3_3 17 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 124 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 124 (accept_3_3 14 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 124 (Polychromatic418967fa.accept_17_13_10_5_1_2566 13 61 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 124
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 12 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 124 (accept_3_3 11 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 124 (accept_3_3 8 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 124 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 61 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 124
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 124 (accept_3_3 5 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  124 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 124 (accept_3_3 2 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 124 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 61 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  124))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 124 (allA_succ_of_accept 59 60 124
  (accept_3_3 59 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 124 2 29 30 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 60 124
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 60 124 4 14 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 60 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 60 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 124 2 27 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 124 (accept_3_3 53 60 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 124 4 13 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 124 2 25 30 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 124
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 124 4 12 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 124 (accept_3_3 47 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60
  124 2 23 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  60 124 (Polychromatic418967fa.accept_19_7_3_10_1_4674 45 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 60 124 4 11 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 60 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 124 2 21 30 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 124 (accept_3_3 41 60 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 124 4 10 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 124
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 60 124 2 19 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 60 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 60 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 124 4 9 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 124 (accept_3_3 35 60 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 60 124 2 17 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 60 124 (Polychromatic418967fa.accept_18_15_6_16_1_4730 33 60 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 124 4 8 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 124
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 124 2 15 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 124 (accept_3_3 29 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60
  124 4 7 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  60 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 60 124 2 13 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 60 124 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 60 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 124 4 6 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 124 (accept_3_3 23 60 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 124 2 11 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 124 4 5 15 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 124
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 124 2 9 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 124 (accept_3_3 17 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60
  124 4 4 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  60 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 60 124 2 7 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 60 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 124 4 3 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 124 (accept_3_3 11 60 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 124 2 5 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 60 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 124 4 2 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 124
  (Polychromatic418967fa.accept_17_7_9_5_1_2588 7 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 124 2 3 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 124 (accept_3_3 5 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 124
  4 1 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60
  124 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 124 2 1 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 124))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 124 (allA_of_3_1 59 59 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 124
  (allA_succ_of_accept 57 58 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 58 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 58 124 2 28 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 58
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 124 2 27 29 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 124 (accept_3_3 53
  58 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 124 2 26 29 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 124
  (Polychromatic418967fa.accept_9_6_4_7_1_300 51 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 58 124 2 25 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 58 124 (Polychromatic418967fa.accept_10_9_8_4_1_970 49 58 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 124 2 24 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 124 (accept_3_3 47 58 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 124 2 23 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 58 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 124 2 22 29 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 124
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 124 2 21 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 58 124 (accept_3_3 41 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58
  124 2 20 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  58 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 58 124 2 19 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 58 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 124 2 18 29 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 124 (accept_3_3 35 58 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 124 2 17 29 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 124
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 58 124 2 16 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 58 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 58 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 124 2 15 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 124 (accept_3_3 29 58 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 124 2 14 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 124 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 58 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 124 2 13 29 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 124
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 124 2 12 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 58 124 (accept_3_3 23 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58
  124 2 11 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  58 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 58 124 2 10 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 58 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 58 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 124 2 9 29 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 124 (accept_3_3 17 58 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58 124 2 8 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 58 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 58 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 124 2 7 29 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 124
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 58 124 2 6 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 58 124 (accept_3_3 11 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58
  124 2 5 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  58 124 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 58 124 2 4 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 58 124 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 58 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 124 2 3 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 124 (accept_3_3 5 58 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 124 2 2 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 58 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 58 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 124 2 1 29 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 124
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 124)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 124 (allA_succ_of_accept 56
  57 124 (accept_3_3 56 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 124
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 124 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 124 (accept_3_3 53 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 51
  57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 124 (accept_3_3 50 57
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 124 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 124
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 124 (accept_3_3 47 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 124 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 124 (accept_3_3 44 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 124
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 124 (accept_3_3 41 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 124 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 124 (accept_3_3 38 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 124
  (Polychromatic418967fa.accept_16_4_9_12_1_4829 36 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 124 (accept_3_3 35 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 124 (accept_3_3 32 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 124
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 124 (accept_3_3 29 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 124 (accept_3_3 26 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 124
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 124 (accept_3_3 23 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 124 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 124 (accept_3_3 20 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 124
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 124 (accept_3_3 17 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 124 (Polychromatic418967fa.accept_15_1_12_4_1_2022 16 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 124 (accept_3_3 14 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 124
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 124 (accept_3_3 11 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 124 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 124 (accept_3_3 8 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 124
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 124 (accept_3_3 5 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  124 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 124 (accept_3_3 2 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 124)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 124 (allA_of_3_1 56 56 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 124
  (allA_succ_of_accept 54 55 124 (Polychromatic418967fa.accept_15_9_10_4_1_2055 54 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 124 (accept_3_3 53 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 124 (Polychromatic418967fa.accept_15_7_10_4_1_151 52 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 124 (accept_3_3 50 55
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 124
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 124 (accept_3_3 47 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 124 (accept_3_3 44 55
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 124 (Polychromatic418967fa.accept_7_1_6_5_1_39
  43 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 124
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 124 (accept_3_3 41 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 124 (accept_3_3 38 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 124 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 55 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 124
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 124 (accept_3_3 35 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 124 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 124 (accept_3_3 32 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 124 (accept_3_3 29 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 124 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 124 (accept_3_3 26 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 55 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 124
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 124 (accept_3_3 23 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 124 (accept_3_3 20 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 55 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 124
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 124 (accept_3_3 17 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 124 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 124 (accept_3_3 14 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 55 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 124 (accept_3_3 11 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 124 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 124 (accept_3_3 8 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 124 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 55 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 124
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 124 (accept_3_3 5 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  124 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 124 (accept_3_3 2 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 124)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 124 (allA_succ_of_accept 53 54 124 (accept_3_3 53 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 124 2 26 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 124 (Polychromatic418967fa.accept_11_7_10_3_1_633 51 54 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 124 2 25 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 124 (Polychromatic418967fa.accept_20_9_14_4_1_4540
  49 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 124 2 24 27 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 124 (accept_3_3 47
  54 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 124 2 23 27 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 124
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 124 2 22 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 124 (Polychromatic418967fa.accept_15_13_9_4_1_3892 43 54 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 124 2 21 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 124 (accept_3_3 41 54 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 124 2 20 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 124 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 54 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 124 2 19 27 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 124
  (Polychromatic418967fa.accept_22_15_10_14_1_6027 37 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 54 124 2 18 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 54 124 (accept_3_3 35 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 124 2 17 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 124 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 124 2 16 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 124 (Polychromatic418967fa.accept_13_5_2_7_1_2414
  31 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 124 2 15 27 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 124 (accept_3_3 29
  54 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 124 2 14 27 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 124
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 124 2 13 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 124 (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 54 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 124 2 12 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 124 (accept_3_3 23 54 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 124 2 11 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 124 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 124 2 10 27 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 124
  (Polychromatic418967fa.accept_17_2_3_5_1_763 19 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 124 2 9 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 124 (accept_3_3 17 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  124 2 8 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 124 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 124 2 7 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 54 124 (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 54 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 124 2 6 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 124 (accept_3_3 11 54 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 124 2 5 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 54 124 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 54 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 124 2 4 27 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 124
  (Polychromatic418967fa.accept_11_7_10_3_1_633 7 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 124 2 3 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 124 (accept_3_3 5 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 124
  2 2 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54
  124 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 124 2 1 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 124 (Polychromatic418967fa.accept_19_1_16_10_1_6026 1 54 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 124)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  124 (allA_of_3_1 53 53 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 124 (allA_succ_of_accept 51 52 124
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 124 2 25 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 124 (Polychromatic418967fa.accept_11_5_8_3_1_66 49 52 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 124 4 12 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 124 (accept_3_3 47 52 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 124 2 23 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 124 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 52
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 124 4 11 13 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 124
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 124 2 21 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 124 (accept_3_3 41 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  124 4 10 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 124 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 124 2 19 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 52 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 124 4 9 13 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 124 (accept_3_3 35 52 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 124 2 17 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 124 (Polychromatic418967fa.accept_14_5_10_12_1_1454
  33 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 124 4 8 13 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 124
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 31 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 124 2 15 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 124 (accept_3_3 29 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  124 4 7 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 124 2 13 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 124 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 52 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 124 4 6 13 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 124 (accept_3_3 23 52 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 124 2 11 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 124 (Polychromatic418967fa.accept_16_5_4_12_1_3800
  21 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 124 4 5 13 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 124
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 19 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 124 2 9 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 124 (accept_3_3 17 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  124 4 4 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 124 2 7 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 124 (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 52 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 124 4 3 13 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 124 (accept_3_3 11 52 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 124 2 5 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 52 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 124 4 2 13 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 124
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 124 2 3 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 124 (accept_3_3 5 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 124
  4 1 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  124 (Polychromatic418967fa.accept_15_3_7_4_1_1225 3 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 52 124 2 1 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 52 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 52 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 124))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 124 (allA_succ_of_accept 50 51 124 (accept_3_3 50 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 51 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 124 (accept_3_3 47 51 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 46
  51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 124
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 124 (accept_3_3 44 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 124 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 124 (accept_3_3 41 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 124 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 51 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 124
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 124 (accept_3_3 38 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 124 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 51 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 124 (accept_3_3 35 51 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 124 (Polychromatic418967fa.accept_13_8_12_7_1_2442 34 51
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 124
  (Polychromatic418967fa.accept_20_13_11_4_1_2042 33 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 124 (accept_3_3 32 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 124 (accept_3_3 29 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 51 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 124
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 124 (accept_3_3 26 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 124 (accept_3_3 23 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 124 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 51 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 124
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 124 (accept_3_3 20 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 124 (accept_3_3 17 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 124 (Polychromatic418967fa.accept_19_16_13_10_1_6025 16 51 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 124
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 124 (accept_3_3 14 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 124 (accept_3_3 11 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 51 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 124
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 124 (accept_3_3 8 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 124 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 124 (accept_3_3 5 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 124 (accept_3_3 2 51 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  124))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 124 (allA_of_3_1 50 50 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 124 (allA_succ_of_accept 48 49 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 124 (accept_3_3 47 49 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 46
  49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 124 (accept_3_3 44 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 124 (Polychromatic418967fa.accept_10_3_9_4_1_960 43 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 124 (accept_3_3 41 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 124 (Polychromatic418967fa.accept_16_8_1_12_1_984 40 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 124 (accept_3_3 38 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 124 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 124 (Polychromatic418967fa.accept_16_4_1_12_1_1792 36 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 124 (accept_3_3 35 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 49 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 124 (accept_3_3 32 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 124 (Polychromatic418967fa.accept_19_12_11_10_1_6024 31 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 124 (accept_3_3 29 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 124 (accept_3_3 26 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 124 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 124 (accept_3_3 23 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 124 (accept_3_3 20 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 124 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 124 (accept_3_3 17 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 124 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 124 (accept_3_3 14 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 124 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 124 (accept_3_3 11 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 124 (accept_3_3 8 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  124 (Polychromatic418967fa.accept_17_7_15_5_1_3649 7 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 124 (accept_3_3 5 49 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 124 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 124 (accept_3_3 2 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  124 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 124))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 124 (allA_succ_of_accept 47 48 124
  (accept_3_3 47 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 124 2 23 24 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 124
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 124 4 11 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 124 2 21 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 124 (accept_3_3 41 48 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 124 4 10 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 124 2 19 24 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 124
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 124 4 9 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 124 (accept_3_3 35 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  124 2 17 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  48 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 124 4 8 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 124 2 15 24 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 124 (accept_3_3 29 48 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 124 4 7 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 124 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 48
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 124 2 13 24 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 124
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 124 4 6 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 124 (accept_3_3 23 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48
  124 2 11 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  48 124 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 48 124 4 5 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 124 2 9 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 124 (accept_3_3 17 48 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 124 4 4 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 48 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 124 2 7 24 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 124
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 124 4 3 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 124 (accept_3_3 11 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48
  124 2 5 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  48 124 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 48 124 4 2 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 48 124 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 48 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 124 2 3 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 124 (accept_3_3 5 48 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 124 4 1 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 48 124 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 48 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 124 2 1 24 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 124
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 124)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 124 (allA_of_3_1 47 47 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 124 (allA_succ_of_accept 45 46 124
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 124 2 22 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 46 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 124 2 21 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 124 (accept_3_3 41 46 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 124 2 20 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 46 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 124 2 19 23 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 124
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 124 2 18 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 124 (accept_3_3 35 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  124 2 17 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 124 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 124 2 16 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 46 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 124 2 15 23 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 124 (accept_3_3 29 46 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 124 2 14 23 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 124
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 124 2 13 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 124 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 46 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 124 2 12 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 124 (accept_3_3 23 46 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 124 2 11 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 46 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 124 2 10 23 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 124
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 124 2 9 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 124 (accept_3_3 17 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  124 2 8 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 124 2 7 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 46 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 124 2 6 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 124 (accept_3_3 11 46 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 124 2 5 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 46 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 46 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 124 2 4 23 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 124
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 124 2 3 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 124 (accept_3_3 5 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 124
  2 2 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  124 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 124 2 1 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 46 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 124)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 124
  (allA_succ_of_accept 44 45 124 (accept_3_3 44 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  45 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 45 124 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 124 (accept_3_3 41 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 124 (Polychromatic418967fa.accept_13_1_6_7_1_550 40 45 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 124
  (Polychromatic418967fa.accept_10_9_5_4_1_966 39 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 124 (accept_3_3 38 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  45 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 124 (accept_3_3 35 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 124 (Polychromatic418967fa.accept_27_7_18_16_1_4108 34 45 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 124
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 124 (accept_3_3 32 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  45 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 45 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 124 (accept_3_3 29 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 124 (Polychromatic418967fa.accept_19_9_7_10_1_1170 28 45 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 124
  (Polychromatic418967fa.accept_13_1_6_7_1_550 27 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 124 (accept_3_3 26 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  45 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 124 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 124 (accept_3_3 23 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 45 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 124
  (Polychromatic418967fa.accept_10_1_5_4_1_276 21 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 124 (accept_3_3 20 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  45 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 124 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 124 (accept_3_3 17 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 45 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 124
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 124 (accept_3_3 14 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 124 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 45 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 124 (accept_3_3 11 45 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 124 (Polychromatic418967fa.accept_16_10_13_12_1_4873 10 45
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 124
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 124 (accept_3_3 8 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 45 124 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 45 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 124 (accept_3_3 5 45 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 45 124 (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 124 (Polychromatic418967fa.accept_19_3_7_10_1_6023
  3 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 124 (accept_3_3 2 45
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  124))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 124 (allA_of_3_1 44 44 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 124 (allA_succ_of_accept 42 43 124 (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 43 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 124 (accept_3_3 41 43 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 124 (Polychromatic418967fa.accept_11_7_10_3_1_633
  40 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 124 (accept_3_3 38 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 124 (Polychromatic418967fa.accept_10_7_3_4_1_978 37 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 124 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 124 (accept_3_3 35 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 43 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 124 (accept_3_3 32 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 124 (Polychromatic418967fa.accept_17_13_9_5_1_6022 30 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 124 (accept_3_3 29 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 124 (Polychromatic418967fa.accept_21_7_1_19_1_6021 28 43
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 124 (accept_3_3 26 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 124 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 124 (accept_3_3 23 43 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 124 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 124 (accept_3_3 20 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 124 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 124 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 43 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 124 (accept_3_3 17 43 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 124 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 124 (accept_3_3 14 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 124 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 124 (accept_3_3 11 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 43 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 124
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 124 (accept_3_3 8 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  124 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 124 (accept_3_3 5 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 124 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 43 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 124 (accept_3_3 2 43 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 124 (Polychromatic418967fa.accept_16_1_11_12_1_1774
  1 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  124))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 124 (allA_succ_of_accept 41 42 124 (accept_3_3 41 42 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 124 2 20 21 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 124
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 124 2 19 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 42 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 124 2 18 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 124 (accept_3_3 35 42 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 124 2 17 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 124 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 124 2 16 21 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 124
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 124 2 15 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 124 (accept_3_3 29 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42
  124 2 14 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  42 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 42 124 2 13 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 42 124 (Polychromatic418967fa.accept_19_6_4_10_1_3342 25 42 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 124 2 12 21 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 124 (accept_3_3 23 42 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 124 2 11 21 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 124
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 124 2 10 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 124 2 9 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 124 (accept_3_3 17 42 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 124 2 8 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 124 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 42 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 124 2 7 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 124 (Polychromatic418967fa.accept_9_4_6_7_1_286 13
  42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 124 2 6 21 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 124 (accept_3_3 11
  42 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 124 2 5 21 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 124
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 124 2 4 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 42 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 124 2 3 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 124 (accept_3_3 5 42 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 124 2 2 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 124 2 1 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  124)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 124 (allA_of_3_1 41 41 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 124 (allA_succ_of_accept 39 40 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 40 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 124 2 19 20 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 124
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 124 4 9 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 40 124 (accept_3_3 35 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40
  124 2 17 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  40 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 40 124 4 8 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 40 124 (Polychromatic418967fa.accept_16_15_8_12_1_2737 31 40 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 124 2 15 20 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 124 (accept_3_3 29 40 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 124 4 7 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40 124 (Polychromatic418967fa.accept_16_11_8_12_1_1767
  27 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 124 2 13 20 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 124
  (Polychromatic418967fa.accept_16_9_8_12_1_979 25 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 40 124 4 6 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 40 124 (accept_3_3 23 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40
  124 2 11 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  40 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 40 124 4 5 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 40 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 124 2 9 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 124 (accept_3_3 17 40 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 124 4 4 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 40 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 40 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 124 2 7 20 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 124
  (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 124 4 3 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 124 (accept_3_3 11 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  124 2 5 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  40 124 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 40 124 4 2 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 40 124 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 40 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 124 2 3 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 124 (accept_3_3 5 40 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 124 4 1 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 40 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 40 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 124 2 1 20 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 124
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 124)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 124 (allA_succ_of_accept 38 39 124 (accept_3_3
  38 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 124
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 124 (accept_3_3 35 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 33
  39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 124 (accept_3_3 32 39
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 124 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 124
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 124 (accept_3_3 29 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 124 (accept_3_3 26 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 124
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 124 (accept_3_3 23 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 124 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 124 (accept_3_3 20 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 124
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 124 (accept_3_3 17 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 124 (accept_3_3 14 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 124
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 124 (accept_3_3 11 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 124 (accept_3_3 8 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 124
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 124 (accept_3_3 5 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  124 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 124 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 124 (accept_3_3 2 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 124))))))))))))))))))))))))))))))))))))))) (allB_succ 38 124
  (allA_of_3_1 38 38 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 124 (allA_succ_of_accept 36 37 124
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 36 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 124 (accept_3_3 35 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 124 (accept_3_3 32 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 37 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 124 (accept_3_3 29 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 124 (Polychromatic418967fa.accept_18_10_1_16_1_579 28 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 124 (accept_3_3 26 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 124
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 124 (accept_3_3 23 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 124 (accept_3_3 20 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 124 (Polychromatic418967fa.accept_17_2_3_5_1_763 19 37 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 124
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 124 (accept_3_3 17 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 124 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 124 (accept_3_3 14 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 37 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 124 (accept_3_3 11 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 124 (accept_3_3 8 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 124 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 37 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 124
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 124 (accept_3_3 5 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  124 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 124 (accept_3_3 2 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 124 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 37 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 124))))))))))))))))))))))))))))))))))))) (allB_succ 36 124
  (allA_succ_of_accept 35 36 124 (accept_3_3 35 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36
  124 2 17 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  36 124 (Polychromatic418967fa.accept_16_1_4_12_1_376 33 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 36 124 4 8 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 36 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 124 2 15 18 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 124 (accept_3_3 29 36 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 124 4 7 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 124 2 13 18 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 124
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 124 4 6 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 124 (accept_3_3 23 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36
  124 2 11 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  36 124 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 36 124 4 5 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 124 (Polychromatic418967fa.accept_16_3_4_12_1_3799 19 36 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 124 2 9 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 124 (accept_3_3 17 36 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 124 4 4 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 36 124 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 36 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 124 2 7 18 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 124
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 124 4 3 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 124 (accept_3_3 11 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36
  124 2 5 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  36 124 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 36 124 4 2 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 36 124 (Polychromatic418967fa.accept_16_7_4_12_1_1806 7 36 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 124 2 3 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 124 (accept_3_3 5 36 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 124 4 1 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 36 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 124 2 1 18 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 124
  (Polychromatic418967fa.accept_16_1_4_12_1_376 1 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 124)))))))))))))))))))))))))))))))))))) (allB_succ 35 124 (allA_of_3_1 35 35 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 124 (allA_succ_of_accept 33 34 124 (Polychromatic418967fa.accept_16_1_2_12_1_1757
  33 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 124 2 16 17 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 124
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 124 2 15 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 34 124 (accept_3_3 29 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34
  124 2 14 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  34 124 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 34 124 2 13 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 34 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 34 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 124 2 12 17 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 124 (accept_3_3 23 34 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 124 2 11 17 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 124
  (Polychromatic418967fa.accept_23_21_11_9_1_6020 21 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 124 2 10 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 124 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 34 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 124 2 9 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 124 (accept_3_3 17 34 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 124 2 8 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 34 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 124 2 7 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 124 (Polychromatic418967fa.accept_11_2_1_3_1_683 13
  34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 124 2 6 17 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 124 (accept_3_3 11
  34 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 124 2 5 17 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 124
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 124 2 4 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 124 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 34 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 124 2 3 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 124 (accept_3_3 5 34 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 124 2 2 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 124 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 34 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 124 2 1 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 34
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 124))))))))))))))))))))))))))))))))))
  (allB_succ 33 124 (allA_succ_of_accept 32 33 124 (accept_3_3 32 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 33 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 124 (accept_3_3 29 33 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 28
  33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 124
  (Polychromatic418967fa.accept_10_7_3_4_1_978 27 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 124 (accept_3_3 26 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 124 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 33 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 124 (accept_3_3 23 33 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 124 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 33 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 124
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 124 (accept_3_3 20 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 124 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 33 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 124 (accept_3_3 17 33 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 124 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 33 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 124
  (Polychromatic418967fa.accept_19_15_14_10_1_4667 15 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 124 (accept_3_3 14 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 124 (accept_3_3 11 33 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 10
  33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 124
  (Polychromatic418967fa.accept_10_9_3_4_1_985 9 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 124 (accept_3_3 8 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 124 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 124 (accept_3_3 5 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 124 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 33 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 124 (accept_3_3 2 33 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 124)))))))))))))))))))))))))))))))))
  (allB_succ 32 124 (allA_of_3_1 32 32 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 124
  (allA_succ_of_accept 30 31 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 31 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 124 (accept_3_3 29 31 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 124 (accept_3_3 26 31
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 124
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 124 (accept_3_3 23 31 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 31 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 124 (accept_3_3 20 31
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 124 (Polychromatic418967fa.accept_8_3_7_4_1_42
  19 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 124
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 124 (accept_3_3 17 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 124 (accept_3_3 14 31 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 124 (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 31 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 124
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 124 (accept_3_3 11 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 124 (accept_3_3 8 31 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 124 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 31 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 124
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 124 (accept_3_3 5 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  124 (Polychromatic418967fa.accept_16_4_15_12_1_1745 4 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 124 (accept_3_3 2 31 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 31 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 124))))))))))))))))))))))))))))))) (allB_succ 30 124
  (allA_succ_of_accept 29 30 124 (accept_3_3 29 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  124 2 14 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 124 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 124 2 13 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 30 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 124 2 12 15 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 124 (accept_3_3 23 30 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 124 2 11 15 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 124
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 124 2 10 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 30 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 124 2 9 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 124 (accept_3_3 17 30 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 124 2 8 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 30 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 124 2 7 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 124 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  30 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 124 2 6 15 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 124 (accept_3_3 11
  30 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 124 2 5 15 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 124
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 124 2 4 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 124 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 30 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 124 2 3 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 124 (accept_3_3 5 30 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 124 2 2 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 30 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 124 2 1 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 30
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 124))))))))))))))))))))))))))))))
  (allB_succ 29 124 (allA_of_3_1 29 29 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 124
  (allA_succ_of_accept 27 28 124 (Polychromatic418967fa.accept_23_4_5_9_1_6019 27 28 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 124 2 13 14 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 124 (Polychromatic418967fa.accept_15_10_13_4_1_1210
  25 28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 124 4 6 7 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 124 (accept_3_3 23
  28 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 124 2 11 14 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 124 4 5 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 124 (Polychromatic418967fa.accept_10_9_8_4_1_970 19 28 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 124 2 9 14 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 124 (accept_3_3 17 28 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 28 124 4 4 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 28 124 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 28 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 124 2 7 14 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 124 4 3 7 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 124 (accept_3_3 11
  28 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 124 2 5 14 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 124
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 124 4 2 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 124 (Polychromatic418967fa.accept_17_7_11_5_1_3539 7 28 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 124 2 3 14 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 124 (accept_3_3 5 28 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 124 4 1 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 28 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 124 2 1 14 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 124 (Polychromatic418967fa.accept_18_1_10_16_1_566 1
  28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 124))))))))))))))))))))))))))))
  (allB_succ 27 124 (allA_succ_of_accept 26 27 124 (accept_3_3 26 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 27 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 124 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 27
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 124 (accept_3_3 23 27 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 22
  27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 124
  (Polychromatic418967fa.accept_10_1_7_4_1_968 21 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 124 (accept_3_3 20 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 27 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 124 (accept_3_3 17 27 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 124 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 27 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 124
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 124 (accept_3_3 14 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 124 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 27 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 124 (accept_3_3 11 27 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 124 (Polychromatic418967fa.accept_16_10_11_12_1_4835 10 27 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 124
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 124 (accept_3_3 8 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 124 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 124 (accept_3_3 5 27 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 124 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 27 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 124 (Polychromatic418967fa.accept_10_3_7_4_1_584 3
  27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 124 (accept_3_3 2 27 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 27
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 124)))))))))))))))))))))))))))
  (allB_succ 26 124 (allA_of_3_1 26 26 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 124
  (allA_succ_of_accept 24 25 124 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 124 (accept_3_3 23 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 25 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 124 (accept_3_3 20 25
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 124
  (Polychromatic418967fa.accept_10_9_5_4_1_966 19 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 124 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 124 (accept_3_3 17 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 25 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15
  25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 124 (accept_3_3 14 25
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 124
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 25 124 (Polychromatic418967fa.accept_17_12_8_5_1_6018 12 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 124 (accept_3_3 11 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 25 124 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 25 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 124 (accept_3_3 8 25 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 124 (Polychromatic418967fa.accept_15_7_10_4_1_151 7
  25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 124
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 124 (accept_3_3 5 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  124 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 25 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 124 (accept_3_3 2 25 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 124))))))))))))))))))))))))) (allB_succ 24 124
  (allA_succ_of_accept 23 24 124 (accept_3_3 23 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24
  124 2 11 12 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  24 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 124 4 5 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 24 124 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 124 2 9 12 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 124 (accept_3_3 17 24 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 124 4 4 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 24 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 124 2 7 12 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 124
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 124 4 3 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 124 (accept_3_3 11 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  124 2 5 12 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 124 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 124 4 2 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 124 (Polychromatic418967fa.accept_16_7_8_12_1_4902 7 24 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 124 2 3 12 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 124 (accept_3_3 5 24 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 124 4 1 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 124 2 1 12 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 124
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 124)))))))))))))))))))))))) (allB_succ 23 124 (allA_of_3_1 23 23 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 124 (allA_succ_of_accept 21 22 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 22 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 124 2 10 11 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 124
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 124 2 9 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 124 (accept_3_3 17 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  124 2 8 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 124 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 124 2 7 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 22 124 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 22 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 124 2 6 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 124 (accept_3_3 11 22 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 124 2 5 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 22 124 (Polychromatic418967fa.accept_19_9_3_10_1_6017 9 22 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 124 2 4 11 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 124
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 22 124 2 3 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 22 124 (accept_3_3 5 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 124
  2 2 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22
  124 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 22 124 2 1 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 22 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 22 124)))))))))))))))))))))) (allB_succ 21 124 (allA_succ_of_accept 20 21
  124 (accept_3_3 20 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 124
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 124 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 21 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 124 (accept_3_3 17 21 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 124 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 21 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 124 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 124 (accept_3_3 14 21
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 124 (Polychromatic418967fa.accept_6_1_3_4_1_1
  13 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 124
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 124 (accept_3_3 11 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 124 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 124 (accept_3_3 8 21 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 21 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 124
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 124 (accept_3_3 5 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  124 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 124 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 21 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 124 (accept_3_3 2 21 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 124))))))))))))))))))))) (allB_succ 20 124 (allA_of_3_1 20 20
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 124 (allA_succ_of_accept 18 19 124
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 124 (accept_3_3 17 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 124 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 124 (accept_3_3 14 19 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 124 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 19 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 124
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 124 (accept_3_3 11 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 124 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 124 (accept_3_3 8 19 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 124 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 19 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 124
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 124 (accept_3_3 5 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  124 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 124 (accept_3_3 2 19 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 124 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 19 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 124))))))))))))))))))) (allB_succ 18 124 (allA_succ_of_accept 17
  18 124 (accept_3_3 17 18 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 124 2 8 9 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 124
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 18 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 124 2 7 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 124 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 18 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 124 2 6 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 124 (accept_3_3 11 18 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 124 2 5 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 124 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 124 2 4 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 124 (Polychromatic418967fa.accept_15_7_3_4_1_574 7
  18 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 124 2 3 9 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 124 (accept_3_3 5 18
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 124 2 2 9 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 124
  (Polychromatic418967fa.accept_12_3_6_4_1_400 3 18 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 124 2 1 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 124 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 18 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 124)))))))))))))))))) (allB_succ 17 124 (allA_of_3_1 17 17 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 124 (allA_succ_of_accept 15 16 124
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 16 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 124 2 7 8 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 124 (Polychromatic418967fa.accept_19_13_16_10_1_6016 13 16 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 124 4 3 4 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 124 (accept_3_3 11 16 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 124 2 5 8 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 124 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 16 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 124 4 2 4 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 124 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7
  16 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 124 2 3 8 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 124 (accept_3_3 5 16
  124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 124 4 1 4 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 124
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 16 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 124 2 1 8 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 124 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 16 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 124)))))))))))))))) (allB_succ 15 124 (allA_succ_of_accept 14 15 124
  (accept_3_3 14 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 124
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 124 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 15 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 124 (accept_3_3 11 15 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 15 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 124 (Polychromatic418967fa.accept_10_9_5_4_1_966 9
  15 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 124 (accept_3_3 8 15 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 124
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 124 (accept_3_3 5 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  124 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 124 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 124 (accept_3_3 2 15 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 124))))))))))))))) (allB_succ 14 124 (allA_of_3_1 14 14 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 124 (allA_succ_of_accept 12 13 124
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 124 (accept_3_3 11 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 124 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 124 (accept_3_3 8 13 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 124 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 13 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 124
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 124 (accept_3_3 5 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  124 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 124 (accept_3_3 2 13 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 124))))))))))))) (allB_succ 12 124 (allA_succ_of_accept 11 12
  124 (accept_3_3 11 12 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 124 2 5 6 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 124
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 12 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 124 4 2 3 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 124 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 12 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 124 2 3 6 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 124 (accept_3_3 5 12 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 124 4 1 3 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 124 (Polychromatic418967fa.accept_19_3_12_10_1_6015 3 12 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 124 2 1 6 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 124 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 12
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 124)))))))))))) (allB_succ 11 124
  (allA_of_3_1 11 11 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 124 (allA_succ_of_accept 9 10 124
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 10 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 124 2 4 5 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 124 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 10 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 124 2 3 5 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 124 (accept_3_3 5 10 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 124 2 2 5 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 124 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 10 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 124 2 1 5 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 124 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 10
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 124)))))))))) (allB_succ 9 124
  (allA_succ_of_accept 8 9 124 (accept_3_3 8 9 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 124
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 9 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 124 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 9 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 124 (accept_3_3 5 9 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 124 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 9 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 124 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 124 (accept_3_3 2 9 124
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9
  124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 124))))))))) (allB_succ 8 124
  (allA_of_3_1 8 8 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 124 (allA_succ_of_accept 6 7 124
  (Polychromatic418967fa.accept_25_6_7_24_1_6014 6 7 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 124 (accept_3_3 5 7 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 124
  (Polychromatic418967fa.accept_11_4_7_3_1_289 4 7 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 124 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 124 (accept_3_3 2 7 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 124 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 7 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 124))))))) (allB_succ 6 124 (allA_succ_of_accept 5 6 124
  (accept_3_3 5 6 124 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 124 2 2 3 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 124
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 6 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 124 2 1 3 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 124 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 6 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 124)))))) (allB_succ 5 124 (allA_of_3_1 5 5 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 124 (allA_succ_of_accept 3 4 124 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 4 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 124 2 1 2 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 124
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 4 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 124)))) (allB_succ 3 124 (allA_succ_of_accept 2 3 124 (accept_3_3 2 3 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 124 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 124))) (allB_succ 2 124 (allA_of_3_1 2 2 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  124))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


