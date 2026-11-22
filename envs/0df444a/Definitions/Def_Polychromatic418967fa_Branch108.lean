-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch108
-- name    : Polychromatic418967fa_Branch108
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:00.511066+00:00
-- url     : https://prove2.me/theorems/0e98740c-22d1-48d4-8a5c-3c9db308067a
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

def Polychromatic418967fa.branch_108 : allB 108 108 :=
  allB_succ' 2 107 108 (Eq.refl Bool.true) (allA_succ_of_accept 1 107 108 (accept_3_4 1 107 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 108)) (allB_succ' 3 106 108 (Eq.refl Bool.true) (allA_succ_of_gcd 2 106 108 2 1 53
  54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 108
  (Polychromatic418967fa.accept_22_1_18_20_1_4946 1 106 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 106 108))) (allB_succ' 4 105 108 (Eq.refl Bool.true) (allA_succ_of_gcd 3 105 108 3 1 35 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 108
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 105 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 108 (Polychromatic418967fa.accept_17_1_3_6_1_3672 1 105 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105 108)))) (allB_succ' 5 104 108 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  104 108 4 1 26 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 104 108 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 104 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 104 108 2 1 52 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 104 108 (accept_3_4 1 104 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  108))))) (allB_succ' 6 103 108 (Eq.refl Bool.true) (allA_succ_of_accept 5 103 108 (accept_3_5 5 103 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 108 (Polychromatic418967fa.accept_16_4_7_12_1_2734 4 103
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 108
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 103 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 108 (accept_3_5 2 103 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 103 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 108)))))) (allB_succ' 7 102 108 (Eq.refl Bool.true) (allA_succ_of_gcd 6 102 108 6 1 17 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 108
  (Polychromatic418967fa.accept_10_5_2_8_1_135 5 102 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 102 108 2 2 51 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 102 108 3 1 34 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 102 108 2 1 51 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 102 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 102 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102 108))))))) (allB_succ' 8 101 108 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 101 108 (accept_3_4 7 101 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 108 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 101 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 108 (Polychromatic418967fa.accept_13_5_10_4_1_1564 5 101 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 108 (accept_3_4 4 101 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 108 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 101 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 108
  (Polychromatic418967fa.accept_19_2_6_13_1_4941 2 101 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 108 (accept_3_4 1 101 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  108)))))))) (allB_succ' 9 100 108 (Eq.refl Bool.true) (allA_succ_of_gcd 8 100 108 4 2 25 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 108
  (Polychromatic418967fa.accept_13_7_9_4_1_918 7 100 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 108 2 3 50 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 108 (accept_3_5 5 100 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  108 4 1 25 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 108 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 100 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 108 2 1 50 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 100 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 100 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 108))))))))) (allB_succ' 10 99 108 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 99 108 9 1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 99 108 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 99 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 99 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 108 3 2 33 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 108
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 99 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 99 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 108 3 1 33 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 99 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 108
  (Polychromatic418967fa.accept_10_1_9_8_1_123 1 99 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 108)))))))))) (allB_succ' 11 98 108 (Eq.refl Bool.true) (allA_succ_of_gcd 10 98 108 2 5 49 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 108
  (Polychromatic418967fa.accept_13_9_7_4_1_953 9 98 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 98 108 2 4 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 98 108 (accept_3_4 7 98 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 108
  2 3 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 98
  108 (Polychromatic418967fa.accept_15_5_8_3_1_556 5 98 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 98 108 2 2 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 98 108 (Polychromatic418967fa.accept_13_3_7_4_1_435 3 98 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 108 2 1 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 108 (accept_3_4 1 98 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 108))))))))))) (allB_succ' 12 97 108 (Eq.refl Bool.true) (allA_succ_of_accept 11 97 108
  (accept_3_5 11 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 108
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 10 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 97 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 97 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 108 (accept_3_5 8 97 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 97 108 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 97 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 108 (Polychromatic418967fa.accept_19_6_2_13_1_4945
  6 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 108 (accept_3_5 5 97
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 108 (Polychromatic418967fa.accept_7_4_6_3_1_271
  4 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 108
  (Polychromatic418967fa.accept_14_3_13_10_1_761 3 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 108 (accept_3_5 2 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  108 (Polychromatic418967fa.accept_17_1_12_6_1_3735 1 97 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 97 108)))))))))))) (allB_succ' 13 96 108 (Eq.refl Bool.true) (allA_succ_of_gcd 12 96 108 12 1 8
  9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 108
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 96 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 96 108 2 5 48 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 96 108 3 3 32 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 96 108 4 2 24 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 108 (Polychromatic418967fa.accept_19_7_1_13_1_4861 7 96 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 108 6 1 16 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 108 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 96 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 108 4 1 24 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 96 108 3 1 32 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 96 108 2 1 48 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 108))))))))))))) (allB_succ' 14 95 108 (Eq.refl Bool.true) (allA_succ_of_accept 13 95 108 (accept_3_4 13
  95 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 108
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 95 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 108 (accept_3_4 10 95 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 95 108 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 95 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 95
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 108 (accept_3_4 7 95 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 108
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 108 (accept_3_4 4 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  108 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 95 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 95 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 108 (accept_3_4 1 95 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 108)))))))))))))) (allB_succ' 15 94 108 (Eq.refl Bool.true) (allA_succ_of_gcd 14 94 108 2 7
  47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 108
  (Polychromatic418967fa.accept_20_13_14_8_1_4850 13 94 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 94 108 2 6 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 94 108 (accept_3_5 11 94 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94
  108 2 5 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  94 108 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 94 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 94 108 2 4 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 94 108 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 94 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 108 2 3 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 108 (accept_3_5 5 94 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 108 2 2 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 94 108 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 94 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 108 2 1 47 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 108
  (Polychromatic418967fa.accept_13_1_3_4_1_925 1 94 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 108))))))))))))))) (allB_succ' 16 93 108 (Eq.refl Bool.true) (allA_succ_of_gcd 15 93 108 3 5 31 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 108
  (Polychromatic418967fa.accept_17_14_8_6_1_2643 14 93 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 93 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 108 3 4 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 93 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 108
  (Polychromatic418967fa.accept_16_10_13_12_1_4873 10 93 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 93 108 3 3 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 93 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 93 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 108 (Polychromatic418967fa.accept_11_7_5_9_1_884 7
  93 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 108 3 2 31 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 93 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 108 (Polychromatic418967fa.accept_16_4_13_12_1_1740 4 93 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 108 3 1 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 108 (Polychromatic418967fa.accept_21_2_9_3_1_4841 2 93 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 108
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 93 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 108)))))))))))))))) (allB_succ' 17 92 108 (Eq.refl Bool.true) (allA_succ_of_gcd 16 92 108 4 4 23 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 108
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 92 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 92 108 2 7 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 92 108 (accept_3_4 13 92 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92
  108 4 3 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  92 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 92 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 92 108 2 5 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 92 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 92 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 108 4 2 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 108 (accept_3_4 7 92 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 108 2 3 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 92 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 92 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 108 4 1 23 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 108
  (Polychromatic418967fa.accept_13_3_1_4_1_945 3 92 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 108 2 1 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 108 (accept_3_4 1 92 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  108))))))))))))))))) (allB_succ' 18 91 108 (Eq.refl Bool.true) (allA_succ_of_accept 17 91 108 (accept_3_5 17 91 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 108
  (Polychromatic418967fa.accept_19_16_15_13_1_1335 16 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 91 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 108 (accept_3_5 14 91 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 108 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 91 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 108
  (Polychromatic418967fa.accept_21_12_7_3_1_4927 12 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 108 (accept_3_5 11 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 108 (Polychromatic418967fa.accept_16_10_11_12_1_4835 10 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 108 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 91 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 108 (accept_3_5 8 91 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 91 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 108
  (Polychromatic418967fa.accept_11_6_3_9_1_906 6 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 108 (accept_3_5 5 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  108 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 91 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 108 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 91 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 108 (accept_3_5 2 91 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 108 (Polychromatic418967fa.accept_16_1_11_12_1_1774 1 91 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 108)))))))))))))))))) (allB_succ' 19 90 108 (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 90 108 18 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 90 108 (Polychromatic418967fa.accept_14_3_6_10_1_752 17 90 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 108 2 8 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 108 3 5 30 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 108 2 7 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 108
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 90 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 90 108 6 2 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 90 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 90 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 108 2 5 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 108 9 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 90 108 2 4 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 108 (Polychromatic418967fa.accept_11_7_2_9_1_480 7
  90 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 108 6 1 15 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 108
  (Polychromatic418967fa.accept_13_5_12_4_1_449 5 90 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 90 108 2 2 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 90 108 3 1 30 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 90 108 2 1 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 108 (Polychromatic418967fa.accept_17_1_5_6_1_3717 1 90 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90 108))))))))))))))))))) (allB_succ' 20 89 108 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 89 108 (accept_3_4 19 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 108 (Polychromatic418967fa.accept_16_2_9_12_1_46 18 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 108 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 89 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 108 (accept_3_4 16 89 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 89 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 108
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 108 (accept_3_4 13 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 108 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 108 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 89 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 108 (accept_3_4 10 89 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 89 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 108 (accept_3_4 7 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  108 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 89 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 108 (accept_3_4 4 89 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 89 108 (Polychromatic418967fa.accept_16_3_9_12_1_4831 3 89 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 108
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 89 108 (accept_3_4 1 89 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  108)))))))))))))))))))) (allB_succ' 21 88 108 (Eq.refl Bool.true) (allA_succ_of_gcd 20 88 108 4 5 22 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 108
  (Polychromatic418967fa.accept_13_6_10_4_1_957 19 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 108 2 9 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 108 (accept_3_5 17 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  108 4 4 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 108 2 7 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 88 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 108 4 3 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 108 (accept_3_5 11 88 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 108 2 5 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 108 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 88 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 108 4 2 22 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 108
  (Polychromatic418967fa.accept_13_7_10_4_1_919 7 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 108 2 3 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 108 (accept_3_5 5 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 108
  4 1 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  108 (Polychromatic418967fa.accept_16_3_8_12_1_2736 3 88 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 88 108 2 1 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 88 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 88 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 108))))))))))))))))))))) (allB_succ' 22 87 108 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 87 108 3 7 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 87 108 (Polychromatic418967fa.accept_13_7_9_4_1_918 20 87 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 19
  87 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 108 3 6 29 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 108
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 108 (Polychromatic418967fa.accept_19_16_11_13_1_4944 16 87 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 108 3 5 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 108 (Polychromatic418967fa.accept_23_14_18_16_1_4943 14 87
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 108
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 108 3 4 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 87 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 108 (Polychromatic418967fa.accept_20_10_7_8_1_4923 10 87
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 108 3 3 29 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 108
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 108 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 87 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 108 3 2 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 108 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 87 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 108
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 4 87 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 108 3 1 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 108 (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 87 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 108 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 87 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 108)))))))))))))))))))))) (allB_succ' 23 86
  108 (Eq.refl Bool.true) (allA_succ_of_gcd 22 86 108 2 11 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 108 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 86 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 108 2 10 43 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 108 (accept_3_4 19
  86 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 108 2 9 43 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 86 108
  (Polychromatic418967fa.accept_21_17_2_3_1_4942 17 86 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 86 108 2 8 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 86 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 86 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 108 2 7 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 108 (accept_3_4 13 86 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 86 108 2 6 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 86 108 (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 86 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 86 108 2 5 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 86 108 (Polychromatic418967fa.accept_13_9_8_4_1_937 9
  86 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 108 2 4 43 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 108 (accept_3_4 7 86
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 108 2 3 43 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 86 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 86 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 86 108 2 2 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 86 108 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 86 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 108 2 1 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 108 (accept_3_4 1 86 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 108))))))))))))))))))))))) (allB_succ' 24 85 108 (Eq.refl Bool.true) (allA_succ_of_accept 23
  85 108 (accept_3_5 23 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 108
  (Polychromatic418967fa.accept_10_2_5_8_1_139 22 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 85 108 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 108 (accept_3_5 20 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 85 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 85 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 18
  85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 108 (accept_3_5 17 85
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 108
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 85 108 (Polychromatic418967fa.accept_19_15_9_13_1_4838 15 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 108 (accept_3_5 14 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 85 108 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 85 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 12
  85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 108 (accept_3_5 11 85
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 108
  (Polychromatic418967fa.accept_11_10_8_9_1_492 10 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 85 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 108 (accept_3_5 8 85 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 85 108 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 85 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 108 (Polychromatic418967fa.accept_13_6_7_4_1_2264 6
  85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 108 (accept_3_5 5 85 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 4
  85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 108
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 108 (accept_3_5 2 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  108 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 85 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 85 108)))))))))))))))))))))))) (allB_succ' 25 84 108 (Eq.refl Bool.true) (allA_succ_of_gcd 24 84 108 12 2 7
  9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 108
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 84 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 84 108 2 11 42 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 84 108 3 7 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 84 108 4 5 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 108 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 84 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 108 6 3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 108 (Polychromatic418967fa.accept_16_1_4_12_1_376 17 84 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 108 4 4 21 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 84 108 3 5 28 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 108 2 7 42 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 108
  (Polychromatic418967fa.accept_11_2_7_9_1_890 13 84 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 108 12 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 108 (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 84 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 108 2 5 42 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 84 108 3 3 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 84 108 4 2 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 108 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 84 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 108 6 1 14 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 108
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 84 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 108 4 1 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 84 108 3 1 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 84 108 2 1 42 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 108 (Polychromatic418967fa.accept_16_1_4_12_1_376 1 84 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 108))))))))))))))))))))))))) (allB_succ' 26 83 108 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 83 108 (accept_3_4 25 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 108 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 108 (accept_3_4 22 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 83 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 108
  (Polychromatic418967fa.accept_15_5_8_3_1_556 20 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 108 (accept_3_4 19 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 108 (Polychromatic418967fa.accept_14_3_13_10_1_761 17 83 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 108 (accept_3_4 16 83 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 83 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 108
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 108 (accept_3_4 13 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 108 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 108 (accept_3_4 10 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 83 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 108
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 108 (accept_3_4 7 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  108 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 83 108 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 108 (accept_3_4 4 83 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 108 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 83 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 108
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 108 (accept_3_4 1 83 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  108)))))))))))))))))))))))))) (allB_succ' 27 82 108 (Eq.refl Bool.true) (allA_succ_of_gcd 26 82 108 2 13 41 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 108
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 108 2 12 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 82 108 (accept_3_5 23 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82
  108 2 11 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  82 108 (Polychromatic418967fa.accept_19_2_6_13_1_4941 21 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 82 108 2 10 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 82 108 (Polychromatic418967fa.accept_14_5_12_10_1_2985 19 82 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 108 2 9 41 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 108 (accept_3_5 17 82 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82 108 2 8 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 82 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 82 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 108 2 7 41 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 108
  (Polychromatic418967fa.accept_39_13_4_30_1_4940 13 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 82 108 2 6 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 82 108 (accept_3_5 11 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82
  108 2 5 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  82 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 82 108 2 4 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 82 108 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 82 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 108 2 3 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 108 (accept_3_5 5 82 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 108 2 2 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 82 108 (Polychromatic418967fa.accept_17_3_14_6_1_3742 3 82 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 108 2 1 41 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 82 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 108))))))))))))))))))))))))))) (allB_succ' 28 81 108 (Eq.refl Bool.true) (allA_succ_of_gcd 27 81 108 27 1
  3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 108
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 108 (Polychromatic418967fa.accept_13_12_3_4_1_928 25 81 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 108 3 8 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 108 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 81 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 108
  (Polychromatic418967fa.accept_7_1_4_3_1_21 22 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 81 108 3 7 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 81 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 81 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 108 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 81 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 108 9 2 9 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 108
  (Polychromatic418967fa.accept_21_17_18_3_1_4909 17 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 108 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 81 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 108 3 5 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 108 (Polychromatic418967fa.accept_13_1_3_4_1_925 14 81 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 108
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 81 108 3 4 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 81 108 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 81 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 108 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 81
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 108 9 1 9 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 108
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 108 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 81 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 108 3 2 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 81 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 108
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 4 81 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 81 108 3 1 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 81 108 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 81 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 81 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 108)))))))))))))))))))))))))))) (allB_succ'
  29 80 108 (Eq.refl Bool.true) (allA_succ_of_gcd 28 80 108 4 7 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 108 (Polychromatic418967fa.accept_17_10_12_6_1_4917 27 80
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 108 2 13 40 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 108 (accept_3_4 25
  80 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 108 4 6 20 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 108
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 80 108 2 11 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 80 108 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 80 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 108 4 5 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 108 (accept_3_4 19 80 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 80 108 2 9 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 80 108 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 80 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 108 4 4 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 108 (Polychromatic418967fa.accept_19_15_4_13_1_4939
  15 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 108 2 7 40 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 108 (accept_3_4 13
  80 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 108 4 3 20 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 108
  (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 80 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 108 2 5 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 108 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 80 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 108 4 2 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 108 (accept_3_4 7 80 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 80 108 2 3 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 80 108 (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 80 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 108 4 1 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 108 (Polychromatic418967fa.accept_19_3_4_13_1_4864 3
  80 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 108 2 1 40 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 108 (accept_3_4 1 80
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80 108))))))))))))))))))))))))))))) (allB_succ' 30 79 108
  (Eq.refl Bool.true) (allA_succ_of_accept 29 79 108 (accept_3_5 29 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 79 108 (Polychromatic418967fa.accept_19_9_3_13_1_2300 28 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 79 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 108 (accept_3_5 26 79 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 108
  (Polychromatic418967fa.accept_39_25_1_30_1_4938 25 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 79 108 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 108 (accept_3_5 23 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 79 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 79 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 108 (Polychromatic418967fa.accept_10_1_9_8_1_123
  21 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 108 (accept_3_5 20
  79 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 79 108 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 108 (accept_3_5 17 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 79 108 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 79 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 108 (accept_3_5 14 79
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 108
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 79 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 108 (accept_3_5 11 79 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 79 108 (Polychromatic418967fa.accept_13_10_1_4_1_3103 10 79 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 108
  (Polychromatic418967fa.accept_19_9_3_13_1_2300 9 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 108 (accept_3_5 8 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  108 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 108 (accept_3_5 5 79 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 108 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 79 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 108
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 108 (accept_3_5 2 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  108 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 108)))))))))))))))))))))))))))))) (allB_succ' 31 78 108 (Eq.refl Bool.true) (allA_succ_of_gcd 30 78 108 6
  5 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 108
  (Polychromatic418967fa.accept_17_12_10_6_1_3691 29 78 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 108 2 14 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 78 108 3 9 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 78 108 2 13 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 78 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 108 6 4 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 78 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 108 2 11 39 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 108 3 7 26 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 108 2 10 39 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 108
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 78 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 108 6 3 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 108 (Polychromatic418967fa.accept_21_17_15_3_1_4937 17 78 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 108 2 8 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 108 3 5 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 108 2 7 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 108 (Polychromatic418967fa.accept_20_13_18_8_1_4936 13 78
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 108 6 2 13 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 108
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 78 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 108 2 5 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 78 108 3 3 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 78 108 2 4 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 108 (Polychromatic418967fa.accept_19_7_2_13_1_4935 7 78 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 108 6 1 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 78 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 108 2 2 39 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 78 108 3 1 26 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 78 108 2 1 39 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 108
  (Polychromatic418967fa.accept_19_1_2_13_1_4934 1 78 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 108))))))))))))))))))))))))))))))) (allB_succ' 32 77 108 (Eq.refl Bool.true) (allA_succ_of_accept 31 77
  108 (accept_3_4 31 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 108
  (Polychromatic418967fa.accept_20_10_17_8_1_4856 30 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 77 108 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 77 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 108 (accept_3_4 28 77 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 77 108 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 77 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 108
  (Polychromatic418967fa.accept_16_10_13_12_1_4873 26 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 77 108 (accept_3_4 25 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 77 108 (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 77 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 108 (Polychromatic418967fa.accept_21_2_14_3_1_4933 23 77
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 108 (accept_3_4 22 77 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 108 (Polychromatic418967fa.accept_13_8_12_4_1_4858
  21 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 108
  (Polychromatic418967fa.accept_13_7_12_4_1_450 20 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 108 (accept_3_4 19 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 108 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 108 (accept_3_4 16 77 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 108 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 77 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 108
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 108 (accept_3_4 13 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 108 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 108 (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 77 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 108 (accept_3_4 10 77 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 77 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 108
  (Polychromatic418967fa.accept_13_8_12_4_1_4858 8 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 108 (accept_3_4 7 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  108 (Polychromatic418967fa.accept_21_6_14_3_1_4932 6 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 77 108 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 77 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 108 (accept_3_4 4 77 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 108 (Polychromatic418967fa.accept_13_3_12_4_1_110 3 77 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 108
  (Polychromatic418967fa.accept_13_2_12_4_1_943 2 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 108 (accept_3_4 1 77 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  108)))))))))))))))))))))))))))))))) (allB_succ' 33 76 108 (Eq.refl Bool.true) (allA_succ_of_gcd 32 76 108 4 8 19 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 108
  (Polychromatic418967fa.accept_14_3_6_10_1_752 31 76 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 108 2 15 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 108 (accept_3_5 29 76 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  108 4 7 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 108 (Polychromatic418967fa.accept_21_6_13_3_1_4851 27 76 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 108 2 13 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 76 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 108 4 6 19 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 108 (accept_3_5 23 76 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 108 2 11 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 108 (Polychromatic418967fa.accept_13_8_11_4_1_1553
  21 76 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 108 4 5 19 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 108
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 76 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 108 2 9 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 108 (accept_3_5 17 76 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  108 4 4 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 108 (Polychromatic418967fa.accept_13_2_11_4_1_445 15 76 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 108 2 7 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 108 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 76 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 108 4 3 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 108 (accept_3_5 11 76 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 108 2 5 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 76 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 76 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 108 4 2 19 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 108
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 76 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 108 2 3 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 108 (accept_3_5 5 76 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 108
  4 1 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  108 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 76 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 76 108 2 1 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 76 108 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 76 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 108))))))))))))))))))))))))))))))))) (allB_succ' 34 75 108
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 75 108 3 11 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 75 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 75 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 108
  (Polychromatic418967fa.accept_8_7_3_4_1_404 31 75 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 108 3 10 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 75 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 108 (Polychromatic418967fa.accept_19_9_18_13_1_4931 28 75
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 108 3 9 25 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 108
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 75 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 108 (Polychromatic418967fa.accept_20_5_15_8_1_4930 25 75 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 108 3 8 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 75 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 22 75 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 108 3 7 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 108 (Polychromatic418967fa.accept_13_7_10_4_1_919 20 75 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 108 (Polychromatic418967fa.accept_13_6_10_4_1_957 19 75 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 108 3 6 25 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 108
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 75 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 75 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 108 3 5 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 108 (Polychromatic418967fa.accept_13_1_10_4_1_954 14 75 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 108
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 75 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 108 3 4 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 108 (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 75 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 108 (Polychromatic418967fa.accept_16_10_11_12_1_4835 10 75
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 108 3 3 25 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 75 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 75 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 108 3 2 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 108 (Polychromatic418967fa.accept_13_5_10_4_1_1564 5 75 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 108
  (Polychromatic418967fa.accept_16_4_11_12_1_1775 4 75 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 108 3 1 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 75 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 75 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 108))))))))))))))))))))))))))))))))))
  (allB_succ' 35 74 108 (Eq.refl Bool.true) (allA_succ_of_gcd 34 74 108 2 17 37 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 108
  (Polychromatic418967fa.accept_13_7_9_4_1_918 33 74 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 108 2 16 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 74 108 (accept_3_4 31 74 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74
  108 2 15 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  74 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 74 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 74 108 2 14 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 74 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 74 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 108 2 13 37 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 108 (accept_3_4 25 74 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 108 2 12 37 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 108
  (Polychromatic418967fa.accept_19_4_17_13_1_4929 23 74 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 74 108 2 11 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 74 108 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 74 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 108 2 10 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 108 (accept_3_4 19 74 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 108 2 9 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 74 108 (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 74 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 108 2 8 37 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 108
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 74 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 108 2 7 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 108 (accept_3_4 13 74 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  108 2 6 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 108 (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 74 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 108 2 5 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 108 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 74 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 108 2 4 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 108 (accept_3_4 7 74 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 108 2 3 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 108 (Polychromatic418967fa.accept_13_5_9_4_1_441 5 74 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 108 2 2 37 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 108
  (Polychromatic418967fa.accept_16_3_10_12_1_4814 3 74 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 108 2 1 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 108 (accept_3_4 1 74 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  108))))))))))))))))))))))))))))))))))) (allB_succ' 36 73 108 (Eq.refl Bool.true) (allA_succ_of_accept 35 73 108
  (accept_3_5 35 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 108
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 73 108 (Polychromatic418967fa.accept_19_14_16_13_1_3488 33 73 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 108 (accept_3_5 32 73 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 73 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 73 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 108
  (Polychromatic418967fa.accept_19_11_16_13_1_4853 30 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 73 108 (accept_3_5 29 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 73 108 (Polychromatic418967fa.accept_17_11_5_6_1_4928 28 73 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 108 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 73 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 108 (accept_3_5 26 73 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 108 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  25 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 108
  (Polychromatic418967fa.accept_11_2_7_9_1_890 24 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 108 (accept_3_5 23 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 108 (Polychromatic418967fa.accept_13_9_8_4_1_937 22 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 73 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 108 (accept_3_5 20 73 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 108 (Polychromatic418967fa.accept_16_3_9_12_1_4831 19 73 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 108
  (Polychromatic418967fa.accept_16_2_9_12_1_46 18 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 108 (accept_3_5 17 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 108 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 108 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 73 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 108 (accept_3_5 14 73 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 73 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 108
  (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 108 (accept_3_5 11 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 108 (Polychromatic418967fa.accept_13_10_8_4_1_3098 10 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 108 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 73 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 108 (accept_3_5 8 73 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 108 (Polychromatic418967fa.accept_14_7_3_10_1_1364 7 73 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 108
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 108 (accept_3_5 5 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  108 (Polychromatic418967fa.accept_16_4_9_12_1_4829 4 73 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 108 (Polychromatic418967fa.accept_16_3_9_12_1_4831 3 73 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 108 (accept_3_5 2 73 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 73 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 108)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 72 108 (Eq.refl Bool.true) (allA_succ_of_gcd 36 72 108 36 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 108 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 72 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 108 2 17 36 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 72 108 3 11 24 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 72 108 4 8 18 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 108
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 31 72 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 108 6 5 12 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 72 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 72 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 108 4 7 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 108 9 3 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 72 108 2 13 36 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 108 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 72 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 108 12 2 6 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 108
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 23 72 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 72 108 2 11 36 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 72 108 3 7 24 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 72 108 4 5 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 108 18 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 108 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 72 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 108 4 4 18 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 72 108 3 5 24 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 72 108 2 7 36 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 108
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 108 12 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 108 (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 72 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 108 2 5 36 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 108 9 1 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 108 4 2 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 108 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 72 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 108 6 1 12 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 108 4 1 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 72 108 3 1 24 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 72 108 2 1 36 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72 108))))))))))))))))))))))))))))))))))))) (allB_succ' 38 71 108 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 71 108 (accept_3_4 37 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 71 108 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 71 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 108 (accept_3_4 34 71 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 108
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 108 (accept_3_4 31 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 108 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 71 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 108 (accept_3_4 28 71 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 71 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 108
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 108 (accept_3_4 25 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 108 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 108 (accept_3_4 22 71 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 108 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 71 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 108
  (Polychromatic418967fa.accept_13_7_6_4_1_933 20 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 108 (accept_3_4 19 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 108 (Polychromatic418967fa.accept_20_17_11_8_1_4894 17 71 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 108 (accept_3_4 16 71 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 108 (Polychromatic418967fa.accept_13_2_6_4_1_1593 15 71 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 108
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 108 (accept_3_4 13 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 108 (accept_3_4 10 71 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 71 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 108
  (Polychromatic418967fa.accept_15_8_11_3_1_3847 8 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 108 (accept_3_4 7 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  108 (Polychromatic418967fa.accept_15_6_11_3_1_1172 6 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 71 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 108 (accept_3_4 4 71 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 71 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 108
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 108 (accept_3_4 1 71 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  108)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 70 108 (Eq.refl Bool.true) (allA_succ_of_gcd 38 70 108 2 19
  35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 108
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 37 70 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 108 2 18 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 70 108 (accept_3_5 35 70 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70
  108 2 17 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  70 108 (Polychromatic418967fa.accept_21_12_7_3_1_4927 33 70 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 70 108 2 16 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 70 108 (Polychromatic418967fa.accept_21_10_7_3_1_4884 31 70 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 108 2 15 35 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 108 (accept_3_5 29 70 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 108 2 14 35 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 108
  (Polychromatic418967fa.accept_13_1_5_4_1_463 27 70 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 70 108 2 13 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 70 108 (Polychromatic418967fa.accept_13_12_5_4_1_3133 25 70 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 108 2 12 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 108 (accept_3_5 23 70 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 108 2 11 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 108 (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 70 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 108 2 10 35 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 108
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 19 70 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 108 2 9 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 108 (accept_3_5 17 70 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  108 2 8 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  70 108 (Polychromatic418967fa.accept_13_2_5_4_1_3926 15 70 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 108 2 7 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 70 108 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 70 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 108 2 6 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 108 (accept_3_5 11 70 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 108 2 5 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 70 108 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 70 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 108 2 4 35 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 108
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 7 70 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 70 108 2 3 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 70 108 (accept_3_5 5 70 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 108
  2 2 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70
  108 (Polychromatic418967fa.accept_25_3_20_8_1_4926 3 70 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 70 108 2 1 35 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 70 108 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 70 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 108))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 69 108
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 69 108 3 13 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 69 108 (Polychromatic418967fa.accept_15_8_9_3_1_1194 38 69 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 108
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 69 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 69 108 3 12 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 69 108 (Polychromatic418967fa.accept_15_5_9_3_1_528 35 69 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 108 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 69 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 108 3 11 23 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 108
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 69 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 108 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 69 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 108 3 10 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 108 (Polychromatic418967fa.accept_17_12_1_6_1_3680
  29 69 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 108
  (Polychromatic418967fa.accept_11_6_3_9_1_906 28 69 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 69 108 3 9 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 108 (Polychromatic418967fa.accept_16_10_5_12_1_4925 26 69 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 69 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 108 3 8 23 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 108
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 69 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 108 (Polychromatic418967fa.accept_17_5_1_6_1_2615 22 69 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 108 3 7 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 108 (Polychromatic418967fa.accept_15_5_9_3_1_528 20 69 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 108
  (Polychromatic418967fa.accept_17_2_1_6_1_3777 19 69 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 108 3 6 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 69 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 69 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 108 3 5 23 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 108
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 69 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 108 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 69 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 108 3 4 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 69 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 108
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 10 69 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 108 3 3 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 108 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 69 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 108 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 69 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 108 3 2 23 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 108
  (Polychromatic418967fa.accept_15_5_9_3_1_528 5 69 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 69 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 108 3 1 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 69 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 108
  (Polychromatic418967fa.accept_8_1_5_4_1_388 1 69 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 108)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 68 108 (Eq.refl Bool.true) (allA_succ_of_gcd
  40 68 108 4 10 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 108 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 68 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 108 2 19 34 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 108 (accept_3_4 37 68 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 108 4 9 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 68 108 (Polychromatic418967fa.accept_15_5_8_3_1_556 35 68 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 108 2 17 34 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 108
  (Polychromatic418967fa.accept_13_7_3_4_1_459 33 68 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 108 4 8 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 108 (accept_3_4 31 68 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  108 2 15 34 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  68 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 68 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 108 4 7 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 108 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 68 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 108 2 13 34 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 108 (accept_3_4 25 68 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 108 4 6 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 68 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 108 2 11 34 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 108
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 68 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 108 4 5 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 108 (accept_3_4 19 68 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  108 2 9 34 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 108 (Polychromatic418967fa.accept_16_1_4_12_1_376 17 68 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 108 4 4 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 68 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 108 2 7 34 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 108 (accept_3_4 13 68 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 108 4 3 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 68 108 (Polychromatic418967fa.accept_15_11_8_3_1_1943 11 68 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 108 2 5 34 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 108
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 68 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 108 4 2 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 108 (accept_3_4 7 68 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 108
  2 3 34 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  108 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 68 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 108 4 1 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 108 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 68 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 108 2 1 34 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 108 (accept_3_4 1 68 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 108))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 67 108 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 67 108 (accept_3_5 41 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 67 108 (Polychromatic418967fa.accept_15_10_7_3_1_1939 40 67 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 67 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 108 (accept_3_5 38 67 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 108 (Polychromatic418967fa.accept_13_11_2_4_1_1590
  37 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 108
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 108 (accept_3_5 35 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 108 (Polychromatic418967fa.accept_21_12_4_3_1_4924 33 67 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 108 (accept_3_5 32 67 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 67 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 108
  (Polychromatic418967fa.accept_20_10_7_8_1_4923 30 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 108 (accept_3_5 29 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 108 (Polychromatic418967fa.accept_19_9_10_13_1_2291 28 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 67 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 108 (accept_3_5 26 67 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 108 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 67 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 108
  (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 108 (accept_3_5 23 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 108 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 67 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 108 (accept_3_5 20 67 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 108 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 67 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 108
  (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 108 (accept_3_5 17 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 108 (Polychromatic418967fa.accept_19_16_10_13_1_4922 16 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 67 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 108 (accept_3_5 14 67 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 67 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 108
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 108 (accept_3_5 11 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 108 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 108 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 67 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 108 (accept_3_5 8 67 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 67 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 108
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 108 (accept_3_5 5 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  108 (Polychromatic418967fa.accept_15_4_7_3_1_119 4 67 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 108 (Polychromatic418967fa.accept_19_3_10_13_1_3482 3 67 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 108 (accept_3_5 2 67 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 108)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 66
  108 (Eq.refl Bool.true) (allA_succ_of_gcd 42 66 108 6 7 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 108 (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 66 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 108 2 20 33 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 108 3 13 22 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 66 108 2 19 33 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 108
  (Polychromatic418967fa.accept_19_18_9_13_1_3496 37 66 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 108 6 6 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 108 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 66 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 108 2 17 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 108 3 11 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 108 2 16 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 108 (Polychromatic418967fa.accept_13_5_1_4_1_3966
  31 66 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 108 6 5 11 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 108
  (Polychromatic418967fa.accept_13_3_1_4_1_945 29 66 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 108 2 14 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 66 108 3 9 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 66 108 2 13 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 108 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 66 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 108 6 4 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 108 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 66 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 108 2 11 33 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 108 3 7 22 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 108 2 10 33 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 108
  (Polychromatic418967fa.accept_23_19_20_16_1_4921 19 66 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 66 108 6 3 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 66 108 (Polychromatic418967fa.accept_16_1_2_12_1_1757 17 66 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 108 2 8 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 108 3 5 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 108 2 7 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 108 (Polychromatic418967fa.accept_10_3_6_8_1_1169
  13 66 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 108 6 2 11 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 108
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 66 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 108 2 5 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 66 108 3 3 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 66 108 2 4 33 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 108 (Polychromatic418967fa.accept_16_7_2_12_1_1754 7 66 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 108 6 1 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 108 (Polychromatic418967fa.accept_13_5_1_4_1_3966 5 66 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 108 2 2 33 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 108 3 1 22 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 108 2 1 33 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 108
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 66 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 108))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 65 108 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 65 108 (accept_3_4 43 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 65 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 108 (accept_3_4 40 65 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 108 (Polychromatic418967fa.accept_15_9_5_3_1_554 39 65 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 108
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 38 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 108 (accept_3_4 37 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 108 (Polychromatic418967fa.accept_20_15_5_8_1_4920 35 65 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 108 (accept_3_4 34 65 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 65 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 108
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 108 (accept_3_4 31 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 108 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 108 (accept_3_4 28 65 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 65 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 108 (accept_3_4 25 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 108 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 108 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 65 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 108 (accept_3_4 22 65 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 65 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 108
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 108 (accept_3_4 19 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 108 (Polychromatic418967fa.accept_16_2_1_12_1_3798 18 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 108 (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 65 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 108 (accept_3_4 16 65 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 65 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 108
  (Polychromatic418967fa.accept_19_14_8_13_1_4834 14 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 108 (accept_3_4 13 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 108 (Polychromatic418967fa.accept_16_11_1_12_1_1795 11 65 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 108 (accept_3_4 10 65 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 108 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 65 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 108
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 108 (accept_3_4 7 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  108 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 65 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 108 (accept_3_4 4 65 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 108 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 65 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 2
  65 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 108 (accept_3_4 1 65 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 108)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  64 108 (Eq.refl Bool.true) (allA_succ_of_gcd 44 64 108 4 11 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 64 108 (Polychromatic418967fa.accept_19_5_7_13_1_4919 43 64 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 108 2 21 32 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 108 (accept_3_5 41
  64 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 108 4 10 16 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 108
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 108 2 19 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 64 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 108 4 9 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 108 (accept_3_5 35 64 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 64 108 2 17 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 64 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 64 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 108 4 8 16 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 108
  (Polychromatic418967fa.accept_13_5_12_4_1_449 31 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 108 2 15 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 108 (accept_3_5 29 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  108 4 7 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 108 (Polychromatic418967fa.accept_21_6_1_3_1_3399 27 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 108 2 13 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 64 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 108 4 6 16 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 108 (accept_3_5 23 64 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 108 2 11 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 108 (Polychromatic418967fa.accept_13_8_12_4_1_4858
  21 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 108 4 5 16 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 108
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 108 2 9 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 108 (accept_3_5 17 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  108 4 4 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 108 (Polychromatic418967fa.accept_13_2_12_4_1_943 15 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 108 2 7 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 108 (Polychromatic418967fa.accept_23_13_18_16_1_4918 13 64 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 108 4 3 16 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 108 (accept_3_5 11 64 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 108 2 5 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 64 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 108 4 2 16 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 108
  (Polychromatic418967fa.accept_13_7_12_4_1_450 7 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 108 2 3 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 108 (accept_3_5 5 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 108
  4 1 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  108 (Polychromatic418967fa.accept_13_3_12_4_1_110 3 64 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 64 108 2 1 32 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 64 108 (Polychromatic418967fa.accept_15_1_4_3_1_1928 1 64 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 108))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  63 108 (Eq.refl Bool.true) (allA_succ_of_gcd 45 63 108 9 5 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 108 (Polychromatic418967fa.accept_17_10_12_6_1_4917 44 63
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 108
  (Polychromatic418967fa.accept_8_3_7_4_1_42 43 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 63 108 3 14 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 41 63 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 108 (Polychromatic418967fa.accept_16_8_15_12_1_1747 40 63
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 108 3 13 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 108
  (Polychromatic418967fa.accept_13_12_11_4_1_3111 38 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 108 (Polychromatic418967fa.accept_24_13_15_12_1_4916 37 63 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 108 9 4 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 63 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 108
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 34 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 63 108 3 11 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 63 108 (Polychromatic418967fa.accept_11_10_8_9_1_492 32 63 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 63 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 108 3 10 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 108
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 29 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 63 108 (Polychromatic418967fa.accept_13_2_11_4_1_445 28 63 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 108 9 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 108 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  26 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 108
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 63 108 3 8 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 63 108 (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 63 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 108 (Polychromatic418967fa.accept_23_22_17_16_1_4915 22 63
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 108 3 7 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 108
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 20 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 63 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 108 9 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 108 (Polychromatic418967fa.accept_14_3_7_10_1_2146 17 63 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 108
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 108 3 5 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 63 108 (Polychromatic418967fa.accept_20_14_3_8_1_4914 14 63 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 108 (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 63
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 108 3 4 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 108
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 108 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 63 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 108 9 1 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 108 (Polychromatic418967fa.accept_13_8_11_4_1_1553 8 63 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 108
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 63 108 3 2 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 108 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 63 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 108 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 63 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 108 3 1 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 108
  (Polychromatic418967fa.accept_13_2_11_4_1_445 2 63 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 63 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 108)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 62 108
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 62 108 2 23 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 108 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 62 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 108 2 22 31 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 108 (accept_3_4 43 62 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 108 2 21 31 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 108
  (Polychromatic418967fa.accept_26_15_10_4_1_4913 41 62 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 108 2 20 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 62 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 108 2 19 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 108 (accept_3_4 37 62 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 108 2 18 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 108 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 62 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 108 2 17 31 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 108
  (Polychromatic418967fa.accept_13_7_10_4_1_919 33 62 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 108 2 16 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 108 (accept_3_4 31 62 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  108 2 15 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 108 (Polychromatic418967fa.accept_15_14_2_3_1_1980 29 62 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 108 2 14 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 108 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 62 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 108 2 13 31 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 108 (accept_3_4 25 62 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 108 2 12 31 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 108
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 62 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 108 2 11 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 108 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 62 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 108 2 10 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 108 (accept_3_4 19 62 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 108 2 9 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 108 (Polychromatic418967fa.accept_14_3_6_10_1_752 17 62 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 108 2 8 31 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 108
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 62 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 108 2 7 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 108 (accept_3_4 13 62 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  108 2 6 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 62 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 108 2 5 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 62 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 108 2 4 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 108 (accept_3_4 7 62 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 108 2 3 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 108 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 62 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 108 2 2 31 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 108
  (Polychromatic418967fa.accept_14_3_6_10_1_752 3 62 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 108 2 1 31 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 108 (accept_3_4 1 62 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  108))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 61 108 (Eq.refl Bool.true) (allA_succ_of_accept 47
  61 108 (accept_3_5 47 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 61 108
  (Polychromatic418967fa.accept_13_7_9_4_1_918 46 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 61 108 (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 61 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 108 (accept_3_5 44 61 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 61 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 108
  (Polychromatic418967fa.accept_16_10_13_12_1_4873 42 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 61 108 (accept_3_5 41 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 61 108 (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 61 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 108 (Polychromatic418967fa.accept_10_9_1_8_1_755 39 61 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 108 (accept_3_5 38 61 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 37
  61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 108 (accept_3_5 35 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 108 (Polychromatic418967fa.accept_13_8_9_4_1_1552 34 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 108 (accept_3_5 32 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 108 (Polychromatic418967fa.accept_13_5_9_4_1_441 31 61 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 108
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 108 (accept_3_5 29 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 108 (Polychromatic418967fa.accept_15_13_1_3_1_1972 28 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 108 (Polychromatic418967fa.accept_19_8_4_13_1_4912 27 61 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 108 (accept_3_5 26 61 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 61 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 108
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 108 (accept_3_5 23 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 108 (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 108 (accept_3_5 20 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 108 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 61 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 108
  (Polychromatic418967fa.accept_13_5_9_4_1_441 18 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 108 (accept_3_5 17 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 108 (accept_3_5 14 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 108 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 61 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 108
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 108 (accept_3_5 11 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 108 (Polychromatic418967fa.accept_16_10_13_12_1_4873 10 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 108 (accept_3_5 8 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 108 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 61 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 108
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 6 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 108 (accept_3_5 5 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  108 (Polychromatic418967fa.accept_15_4_1_3_1_1922 4 61 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 108 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 108 (accept_3_5 2 61 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 108))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 60 108 (Eq.refl Bool.true) (allA_succ_of_gcd 48 60 108 12 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 108 (Polychromatic418967fa.accept_19_9_3_13_1_2300
  47 60 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 108 2 23 30 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 108 3 15 20 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 108 4 11 15 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 108
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 108 6 7 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 60 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 108 4 10 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 108 3 13 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 60 108 2 19 30 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 108 (Polychromatic418967fa.accept_13_11_8_4_1_3950
  37 60 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 108 12 3 5 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 108
  (Polychromatic418967fa.accept_13_9_8_4_1_937 35 60 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 60 108 2 17 30 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 60 108 3 11 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 60 108 4 8 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 108 (Polychromatic418967fa.accept_19_12_3_13_1_4911 31 60 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 108 6 5 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 108 4 7 15 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 108 3 9 20 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 108 2 13 30 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 108
  (Polychromatic418967fa.accept_13_12_8_4_1_3099 25 60 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 108 12 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 108 (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 60 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 108 2 11 30 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 108 3 7 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 108 4 5 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 108 (Polychromatic418967fa.accept_21_19_18_3_1_4910
  19 60 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 108 6 3 10 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 108
  (Polychromatic418967fa.accept_21_17_18_3_1_4909 17 60 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 60 108 4 4 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 60 108 3 5 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 60 108 2 7 30 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 108 12 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 108 (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 60 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 108 2 5 30 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 108 3 3 20 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 108 4 2 15 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 108
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 60 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 108 6 1 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 108 (Polychromatic418967fa.accept_21_5_18_3_1_4908 5 60 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 108 4 1 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 108 3 1 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 108 2 1 30 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  108))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 59 108 (Eq.refl Bool.true) (allA_succ_of_accept 49
  59 108 (accept_3_4 49 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 108
  (Polychromatic418967fa.accept_13_9_7_4_1_953 48 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 59 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 59 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 108 (accept_3_4 46 59 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 59 108 (Polychromatic418967fa.accept_13_6_7_4_1_2264 45 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 108 (Polychromatic418967fa.accept_10_4_9_8_1_125
  44 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 108 (accept_3_4 43
  59 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 108
  (Polychromatic418967fa.accept_13_3_7_4_1_435 42 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 59 108 (Polychromatic418967fa.accept_10_1_9_8_1_123 41 59 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 108 (accept_3_4 40 59 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 59 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 108 (Polychromatic418967fa.accept_13_12_7_4_1_3124
  38 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 108 (accept_3_4 37
  59 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 108
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 59 108 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 59 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 108 (accept_3_4 34 59 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 59 108 (Polychromatic418967fa.accept_16_1_11_12_1_1774 33 59 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 108
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 32 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 108 (accept_3_4 31 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 108 (Polychromatic418967fa.accept_19_11_2_13_1_4907 30 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 108 (Polychromatic418967fa.accept_13_3_7_4_1_435 29 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 108 (accept_3_4 28 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 108 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 59 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 108
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 26 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 108 (accept_3_4 25 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 108 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 108 (accept_3_4 22 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 108 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 59 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 108
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 108 (accept_3_4 19 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 108 (Polychromatic418967fa.accept_21_18_17_3_1_4906 18 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 108 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 108 (accept_3_4 16 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 59 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 108
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 108 (accept_3_4 13 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 108 (Polychromatic418967fa.accept_13_12_7_4_1_3124 12 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 108 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 108 (accept_3_4 10 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 108 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 59 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 108
  (Polychromatic418967fa.accept_16_8_11_12_1_962 8 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 108 (accept_3_4 7 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  108 (Polychromatic418967fa.accept_13_6_7_4_1_2264 6 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 59 108 (Polychromatic418967fa.accept_22_5_15_20_1_4905 5 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 108 (accept_3_4 4 59 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 108 (Polychromatic418967fa.accept_13_3_7_4_1_435 3 59 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 108
  (Polychromatic418967fa.accept_11_2_4_9_1_484 2 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 108 (accept_3_4 1 59 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  108)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 58 108 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  58 108 2 25 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  49 58 108 (Polychromatic418967fa.accept_13_10_6_4_1_1583 49 58 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 58 108 2 24 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 58 108 (accept_3_5 47 58 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 58 108 2 23 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 58 108 (Polychromatic418967fa.accept_16_13_10_12_1_1811 45 58 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 108 2 22 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 43
  58 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 108 2 21 29 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 108 (accept_3_5 41
  58 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 108 2 20 29 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 108
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 58 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 108 2 19 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 108 (Polychromatic418967fa.accept_13_11_6_4_1_3121 37 58 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 108 2 18 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 108 (accept_3_5 35 58 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 108 2 17 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 58 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 108 2 16 29 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 108
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 31 58 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 108 2 15 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 108 (accept_3_5 29 58 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  108 2 14 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 58 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 108 2 13 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 108 (Polychromatic418967fa.accept_15_10_13_3_1_4816 25 58 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 108 2 12 29 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 108 (accept_3_5 23 58 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 108 2 11 29 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 108
  (Polychromatic418967fa.accept_16_5_10_12_1_4904 21 58 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 108 2 10 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 58 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 108 2 9 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 108 (accept_3_5 17 58 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 108 2 8 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 58 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 108 2 7 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  58 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 108 2 6 29 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 108 (accept_3_5 11
  58 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 108 2 5 29 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 108
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 58 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 108 2 4 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 108 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 58 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 108 2 3 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 108 (accept_3_5 5 58 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 108 2 2 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 108 (Polychromatic418967fa.accept_16_3_10_12_1_4814 3 58 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 108 2 1 29 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 58
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  108))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 57 108 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  57 108 3 17 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  50 57 108 (Polychromatic418967fa.accept_16_2_9_12_1_46 50 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 57 108 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 57 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 108 3 16 19 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 108
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 108 3 15 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 108
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 43 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 108 3 14 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 108 (Polychromatic418967fa.accept_13_2_5_4_1_3926 41 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 57 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 108 3 13 19 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 108
  (Polychromatic418967fa.accept_13_12_5_4_1_3133 38 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 108 3 12 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 108 (Polychromatic418967fa.accept_10_5_7_8_1_1176
  35 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 108
  (Polychromatic418967fa.accept_16_2_9_12_1_46 34 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 108 3 11 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 108 (Polychromatic418967fa.accept_20_11_17_8_1_4903 31 57
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 108 3 10 19 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 108
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 108 (Polychromatic418967fa.accept_13_2_5_4_1_3926 28 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 108 3 9 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 57 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 108
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 108 3 8 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 108 (Polychromatic418967fa.accept_13_9_5_4_1_1591 22 57 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 108 3 7 19 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 108
  (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 108 3 6 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 108 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 57 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 108
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 108 3 5 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 108 (Polychromatic418967fa.accept_13_1_5_4_1_463 14 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 57 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 108 3 4 19 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 108
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 108 (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 108 3 3 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 108 (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 57 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 108
  (Polychromatic418967fa.accept_11_7_2_9_1_480 7 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 108 3 2 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 108 3 1 19 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 108
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 57 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 108 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 57 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 108)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 56
  108 (Eq.refl Bool.true) (allA_succ_of_gcd 52 56 108 4 13 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 108 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 56 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 108 2 25 28 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 108 (accept_3_4 49
  56 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 108 4 12 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 108
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 47 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 108 2 23 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 108 (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 56 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 108 4 11 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 108 (accept_3_4 43 56 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 108 2 21 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 108 (Polychromatic418967fa.accept_16_9_8_12_1_979 41 56 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 108 4 10 14 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 108
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 39 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 108 2 19 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 108 (accept_3_4 37 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  108 4 9 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 108 (Polychromatic418967fa.accept_16_3_8_12_1_2736 35 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 108 2 17 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 108 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 56 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 108 4 8 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 108 (accept_3_4 31 56 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 108 2 15 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 108 (Polychromatic418967fa.accept_15_14_11_3_1_1957
  29 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 108 4 7 14 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 108
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 108 2 13 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 56 108 (accept_3_4 25 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56
  108 4 6 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  56 108 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 56 108 2 11 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 56 108 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 56 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 108 4 5 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 108 (accept_3_4 19 56 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 108 2 9 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 108 (Polychromatic418967fa.accept_16_1_8_12_1_405 17 56 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 108 4 4 14 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 108
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 108 2 7 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 108 (accept_3_4 13 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56
  108 4 3 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  56 108 (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 108 2 5 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 108 (Polychromatic418967fa.accept_16_9_8_12_1_979 9 56 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 108 4 2 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 108 (accept_3_4 7 56 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 108 2 3 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 56 108 (Polychromatic418967fa.accept_16_5_8_12_1_1766 5 56 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 108 4 1 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 108
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 108 2 1 28 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 108 (accept_3_4 1 56 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  108))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 55 108 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 55 108 (accept_3_5 53 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 108 (accept_3_5 50 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 108 (Polychromatic418967fa.accept_19_11_17_13_1_3458 49 55 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 108
  (Polychromatic418967fa.accept_21_6_13_3_1_4851 48 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 108 (accept_3_5 47 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 108 (Polychromatic418967fa.accept_14_3_13_10_1_761 45 55 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 108 (accept_3_5 44 55 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 55 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 108
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 108 (accept_3_5 41 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 108 (Polychromatic418967fa.accept_13_1_3_4_1_925 40 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 108 (accept_3_5 38 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 55 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 108
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 108 (accept_3_5 35 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 108 (Polychromatic418967fa.accept_16_2_7_12_1_3793 34 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 108 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 108 (accept_3_5 32 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 108 (Polychromatic418967fa.accept_14_3_13_10_1_761 31 55 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 108
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 108 (accept_3_5 29 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 108 (Polychromatic418967fa.accept_15_13_10_3_1_1952 28 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 108 (accept_3_5 26 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 55 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 108
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 108 (accept_3_5 23 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 108 (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 55 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 108 (accept_3_5 20 55 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 55 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 108
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 108 (accept_3_5 17 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 108 (Polychromatic418967fa.accept_19_15_17_13_1_4901 15 55 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 108 (accept_3_5 14 55 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 108 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 55 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 108
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 108 (accept_3_5 11 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 108 (Polychromatic418967fa.accept_17_10_4_6_1_3757 10 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 108 (accept_3_5 8 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 108 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 55 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 108
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 108 (accept_3_5 5 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  108 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 55 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 108 (accept_3_5 2 55 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 108 (Polychromatic418967fa.accept_13_1_3_4_1_925 1 55 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 108))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 108 (allA_succ_of_accept 53 54 108 (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 54 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 108 2 26 27 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 54 108 3 17 18 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 54 108 2 25 27 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 108
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 54 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 108 6 8 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 108 (Polychromatic418967fa.accept_14_5_12_10_1_2985 47 54 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 108 2 23 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 54 108 9 5 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 54 108 2 22 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 43
  54 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 108 6 7 9 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 108
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 54 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 108 2 20 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 54 108 3 13 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 54 108 2 19 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 54 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 54 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 108 18 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 108 (Polychromatic418967fa.accept_15_5_9_3_1_528 35 54 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 108 2 17 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 54 108 3 11 18 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 54 108 2 16 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 108
  (Polychromatic418967fa.accept_13_5_2_4_1_3955 31 54 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 108 6 5 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 54 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 108 2 14 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 108 27 1 2 4 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 108 2 13 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 108 (Polychromatic418967fa.accept_13_12_2_4_1_3131
  25 54 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 108 6 4 9 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 108
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 54 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 108 2 11 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 54 108 3 7 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 54 108 2 10 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 54 108 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 54 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 108 18 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 108 (Polychromatic418967fa.accept_19_17_16_13_1_4900 17 54
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 108 2 8 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 108 3 5 18 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 108 2 7 27 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 108
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 54 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 108 6 2 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 108 (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 54 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 108 2 5 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 108 9 1 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 108 2 4 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 108 (Polychromatic418967fa.accept_21_7_12_3_1_4849 7 54 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 108 6 1 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 108
  (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 54 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 54 108 2 2 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 54 108 3 1 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 54 108 2 1 27 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 54 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 108)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  108 (allA_succ_of_accept 52 53 108 (accept_3_4 52 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 108 (accept_3_4 49 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 53 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 108
  (Polychromatic418967fa.accept_17_13_2_6_1_3683 47 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 108 (accept_3_4 46 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 108 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 108 (Polychromatic418967fa.accept_13_5_1_4_1_3966 44 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 108 (accept_3_4 43 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 108 (Polychromatic418967fa.accept_13_3_1_4_1_945 42 53 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 108
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 108 (accept_3_4 40 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 108 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 108 (Polychromatic418967fa.accept_17_4_2_6_1_2629 38 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 108 (accept_3_4 37 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 108
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 108 (accept_3_4 34 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 108 (Polychromatic418967fa.accept_23_9_7_16_1_4899 32 53 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 108 (accept_3_4 31 53 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 108 (Polychromatic418967fa.accept_17_13_2_6_1_3683 30 53
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 108
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 108 (accept_3_4 28 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 108 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 108 (accept_3_4 25 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 108 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 53 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 108
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 108 (accept_3_4 22 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 108 (accept_3_4 19 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 108 (Polychromatic418967fa.accept_13_5_1_4_1_3966 18 53 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 108
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 108 (accept_3_4 16 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 108 (Polychromatic418967fa.accept_19_14_15_13_1_4898 14 53 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 108 (accept_3_4 13 53 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 108 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 53
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 108
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 108 (accept_3_4 10 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 108 (accept_3_4 7 53 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 53 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 108
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 108 (accept_3_4 4 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  108 (Polychromatic418967fa.accept_13_3_1_4_1_945 3 53 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 108 (Polychromatic418967fa.accept_19_2_15_13_1_4897 2 53 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 108 (accept_3_4 1 53 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 108))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 108
  (allA_succ_of_accept 51 52 108 (Polychromatic418967fa.accept_16_3_4_12_1_3799 51 52 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 108 2 25 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 108 (Polychromatic418967fa.accept_15_4_7_3_1_119 49
  52 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 108 4 12 13 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 108 (accept_3_5 47
  52 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 108 2 23 26 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 108
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 108 4 11 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 52 108 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 52 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 108 2 21 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 108 (accept_3_5 41 52 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 108 4 10 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 108 (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 52 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 108 2 19 26 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 108
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 37 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 108 4 9 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 108 (accept_3_5 35 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52
  108 2 17 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  52 108 (Polychromatic418967fa.accept_16_1_4_12_1_376 33 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 52 108 4 8 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 52 108 (Polychromatic418967fa.accept_16_15_4_12_1_2731 31 52 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 108 2 15 26 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 108 (accept_3_5 29 52 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 108 4 7 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 108 (Polychromatic418967fa.accept_15_12_7_3_1_1940
  27 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 108 2 13 26 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 108
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 108 4 6 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 108 (accept_3_5 23 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  108 2 11 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  52 108 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 108 4 5 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 52 108 (Polychromatic418967fa.accept_15_4_7_3_1_119 19 52 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 108 2 9 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 108 (accept_3_5 17 52 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 108 4 4 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 52 108 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 52 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 108 2 7 26 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 108
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 108 4 3 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 108 (accept_3_5 11 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  108 2 5 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 108 (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 108 4 2 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 108 (Polychromatic418967fa.accept_16_7_4_12_1_1806 7 52 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 108 2 3 26 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 108 (accept_3_5 5 52 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 108 4 1 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 108 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 52 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 108 2 1 26 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 108
  (Polychromatic418967fa.accept_16_1_4_12_1_376 1 52 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 108)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 108 (allA_succ_of_accept 50 51 108
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 108 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 108 3 16 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 108
  (Polychromatic418967fa.accept_11_2_7_9_1_890 46 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 108 3 15 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 108 (Polychromatic418967fa.accept_13_5_12_4_1_449 44 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 51 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 108 3 14 17 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 108
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 108 3 13 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 108 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  38 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 108
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 37 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 108 3 12 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 108 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 51 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 108 3 11 17 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 108
  (Polychromatic418967fa.accept_23_9_5_16_1_4895 32 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 108 3 10 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 108
  (Polychromatic418967fa.accept_13_2_12_4_1_943 28 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 108 3 9 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 108 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 51
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 108 3 8 17 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 108
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 108 3 7 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 51 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 108 3 6 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 108 (Polychromatic418967fa.accept_20_17_11_8_1_4894 17 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 108 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 51 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 108 3 5 17 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 108
  (Polychromatic418967fa.accept_21_14_9_3_1_4893 14 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 108 3 4 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 108 (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 51
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 108
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 108 3 3 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 51 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 108 3 2 17 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 108 (Polychromatic418967fa.accept_16_4_3_12_1_4892 4 51 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 108 3 1 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 108 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 51 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 108
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 51 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 108))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 108 (allA_succ_of_accept 49 50 108
  (accept_3_4 49 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 108 2 24 25 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 108
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 108 2 23 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 50 108 (Polychromatic418967fa.accept_13_6_11_4_1_938 45 50 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 108 2 22 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 108 (accept_3_4 43 50 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 108 2 21 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 108 (Polychromatic418967fa.accept_13_2_11_4_1_445 41 50 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 108 2 20 25 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 108
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 108 2 19 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 50 108 (accept_3_4 37 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50
  108 2 18 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  50 108 (Polychromatic418967fa.accept_19_16_12_13_1_4843 35 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 50 108 2 17 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 50 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 50 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 108 2 16 25 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 108 (accept_3_4 31 50 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 108 2 15 25 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 108
  (Polychromatic418967fa.accept_37_29_13_34_1_4891 29 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 108 2 14 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 108 (Polychromatic418967fa.accept_17_10_16_6_1_4890 27 50 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 108 2 13 25 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 108 (accept_3_4 25 50 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 108 2 12 25 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 108
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 108 2 11 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 108 (Polychromatic418967fa.accept_13_8_11_4_1_1553 21 50 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 108 2 10 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 108 (accept_3_4 19 50 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 108 2 9 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 108 (Polychromatic418967fa.accept_15_2_5_3_1_552 17 50 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 108 2 8 25 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 108
  (Polychromatic418967fa.accept_13_2_11_4_1_445 15 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 108 2 7 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 108 (accept_3_4 13 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  108 2 6 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 108 2 5 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 50 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 108 2 4 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 108 (accept_3_4 7 50 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 108 2 3 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 50 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 108 2 2 25 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 108
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 108 2 1 25 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 108 (accept_3_4 1 50 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  108)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 108 (allA_succ_of_accept 48 49 108
  (Polychromatic418967fa.accept_17_14_15_6_1_4819 48 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 108 (accept_3_5 47 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 108 (Polychromatic418967fa.accept_13_7_10_4_1_919 46 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 108 (accept_3_5 44 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 108 (Polychromatic418967fa.accept_16_11_1_12_1_1795 43 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 108
  (Polychromatic418967fa.accept_17_8_15_6_1_4889 42 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 108 (accept_3_5 41 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 108 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 108 (Polychromatic418967fa.accept_14_11_7_10_1_4852 39 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 108 (accept_3_5 38 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 49 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 108
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 36 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 108 (accept_3_5 35 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 108 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 108 (Polychromatic418967fa.accept_13_7_10_4_1_919 33 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 108 (accept_3_5 32 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 108 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 108
  (Polychromatic418967fa.accept_21_9_7_3_1_4888 30 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 108 (accept_3_5 29 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 108 (Polychromatic418967fa.accept_24_4_1_12_1_4887 28 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 108 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 108 (accept_3_5 26 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 108 (Polychromatic418967fa.accept_14_11_7_10_1_4852 25 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 108
  (Polychromatic418967fa.accept_10_4_9_8_1_125 24 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 108 (accept_3_5 23 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 108 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 108 (accept_3_5 20 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 108 (Polychromatic418967fa.accept_13_6_10_4_1_957 19 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 108
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 108 (accept_3_5 17 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 108 (Polychromatic418967fa.accept_15_1_4_3_1_1928 16 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 108 (Polychromatic418967fa.accept_21_15_7_3_1_4886 15 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 108 (accept_3_5 14 49 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 49 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 108
  (Polychromatic418967fa.accept_19_12_11_13_1_4885 12 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 49 108 (accept_3_5 11 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 49 108 (Polychromatic418967fa.accept_21_10_7_3_1_4884 10 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 108 (Polychromatic418967fa.accept_17_9_15_6_1_3744 9 49 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 108 (accept_3_5 8 49 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 108 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7
  49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 108
  (Polychromatic418967fa.accept_13_6_10_4_1_957 6 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 108 (accept_3_5 5 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  108 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 49 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 108 (Polychromatic418967fa.accept_14_3_7_10_1_2146 3 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 108 (accept_3_5 2 49 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 108 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 49 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 108))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 108 (allA_succ_of_accept 47 48 108 (Polychromatic418967fa.accept_13_8_9_4_1_1552 47 48 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 108 2 23 24 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 48 108 3 15 16 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 48 108 4 11 12 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 108
  (Polychromatic418967fa.accept_19_5_10_13_1_4883 43 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 108 6 7 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 108 (Polychromatic418967fa.accept_17_7_14_6_1_4882 41 48 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 108 4 10 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 108 3 13 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 108 2 19 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 37
  48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 108 12 3 4 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 108
  (Polychromatic418967fa.accept_11_2_4_9_1_484 35 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 108 2 17 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 48 108 3 11 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 48 108 4 8 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 108 (Polychromatic418967fa.accept_13_5_9_4_1_441 31 48 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 108 6 5 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 108 (Polychromatic418967fa.accept_21_8_6_3_1_4881 29 48 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 108 4 7 12 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 48 108 3 9 16 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 48 108 2 13 24 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 108
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 108 12 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 108 2 11 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 108 3 7 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 108 4 5 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 108 (Polychromatic418967fa.accept_13_6_9_4_1_2288
  19 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 108 6 3 8 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 108
  (Polychromatic418967fa.accept_14_3_6_10_1_752 17 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 48 108 4 4 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 48 108 3 5 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 48 108 2 7 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 108 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 48 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 108 12 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 108 2 5 24 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 108 3 3 16 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 108 4 2 12 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 108
  (Polychromatic418967fa.accept_13_7_9_4_1_918 7 48 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 108 6 1 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 108 (Polychromatic418967fa.accept_13_5_9_4_1_441 5 48 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 108 4 1 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 108 3 1 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 108 2 1 24 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 108 (Polychromatic418967fa.accept_19_1_10_13_1_4880 1 48 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  108)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 108 (allA_succ_of_accept 46 47 108 (accept_3_4 46 47
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 108
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 108 (accept_3_4 43 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 108 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 108
  (Polychromatic418967fa.accept_17_7_13_6_1_811 41 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 108 (accept_3_4 40 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 108 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 108 (Polychromatic418967fa.accept_13_12_8_4_1_3099 38 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 108 (accept_3_4 37 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 108
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 108 (accept_3_4 34 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 108 (Polychromatic418967fa.accept_22_11_3_20_1_4879 33 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 108 (Polychromatic418967fa.accept_22_10_3_20_1_4878 32 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 108 (accept_3_4 31 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 47 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 108 (accept_3_4 28 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 108 (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 108 (accept_3_4 25 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 108 (Polychromatic418967fa.accept_13_11_8_4_1_3950 24 47
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 108
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 108 (accept_3_4 22 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 108 (Polychromatic418967fa.accept_20_1_7_8_1_4877 21 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 108 (Polychromatic418967fa.accept_15_5_2_3_1_4876 20 47 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 108 (accept_3_4 19 47 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 108 (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 108
  (Polychromatic418967fa.accept_11_6_3_9_1_906 17 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 108 (accept_3_4 16 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 108 (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 108 (accept_3_4 13 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 108 (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 47
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 108
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 108 (accept_3_4 10 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 47 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 108 (accept_3_4 7 47 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 108 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 47 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 108
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 108 (accept_3_4 4 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  108 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 47 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 108 (accept_3_4 1 47 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 108))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 108 (allA_succ_of_accept 45
  46 108 (Polychromatic418967fa.accept_13_6_7_4_1_2264 45 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 46 108 2 22 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 46 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 46 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 108 2 21 23 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 108 (accept_3_5 41 46 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 108 2 20 23 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 108
  (Polychromatic418967fa.accept_19_1_8_13_1_4875 39 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 108 2 19 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 46 108 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 46 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 108 2 18 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 108 (accept_3_5 35 46 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 108 2 17 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 108 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 46 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 108 2 16 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 108
  (Polychromatic418967fa.accept_34_31_12_6_1_4874 31 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 108 2 15 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 46 108 (accept_3_5 29 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46
  108 2 14 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  46 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 46 108 2 13 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 46 108 (Polychromatic418967fa.accept_13_12_7_4_1_3124 25 46 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 108 2 12 23 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 108 (accept_3_5 23 46 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 108 2 11 23 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 108
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 21 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 108 2 10 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 108 (Polychromatic418967fa.accept_13_6_7_4_1_2264 19 46 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 108 2 9 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 108 (accept_3_5 17 46 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 108 2 8 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 46 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 108 2 7 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 13
  46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 108 2 6 23 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 108 (accept_3_5 11
  46 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 108 2 5 23 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 108
  (Polychromatic418967fa.accept_13_9_7_4_1_953 9 46 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 108 2 4 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 108 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 46 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 108 2 3 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 108 (accept_3_5 5 46 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 108 2 2 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 108 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 46 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 108 2 1 23 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 46
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  108)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 108 (allA_succ_of_accept 44 45 108
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 44 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 108 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 108 3 14 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 41
  45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 108
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 40 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 108 3 13 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 108 (Polychromatic418967fa.accept_17_4_11_6_1_3730 38 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 108 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 45 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 108 9 4 5 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 108
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 35 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 108 (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 108 3 11 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 32
  45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 108
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 31 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 108 3 10 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 108 (Polychromatic418967fa.accept_17_12_11_6_1_3729 29 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 108 (Polychromatic418967fa.accept_13_2_6_4_1_1593 28 45 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 108 9 3 5 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 108
  (Polychromatic418967fa.accept_16_10_13_12_1_4873 26 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 45 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 45 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 108 3 8 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 108 (Polychromatic418967fa.accept_10_3_5_8_1_1132
  23 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 108
  (Polychromatic418967fa.accept_10_2_5_8_1_139 22 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 108 3 7 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 108 (Polychromatic418967fa.accept_13_7_6_4_1_933 20 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 108 (Polychromatic418967fa.accept_22_19_1_20_1_4872 19 45
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 108 9 2 5 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 108
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 108 (Polychromatic418967fa.accept_25_16_20_8_1_4871 16 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 108 3 5 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 108 (Polychromatic418967fa.accept_20_14_5_8_1_4870 14 45 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 108
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 108 3 4 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 108 (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 108 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 45
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 108 9 1 5 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 108
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 8 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 108 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 108 3 2 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 108 (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 45 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 108
  (Polychromatic418967fa.accept_16_4_13_12_1_1740 4 45 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 108 3 1 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 45 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 45 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  108))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 108 (allA_succ_of_accept 43 44 108 (accept_3_4 43 44
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 108 2 21 22 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 108
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 108 4 10 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 108 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 44 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 108 2 19 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 108 (accept_3_4 37 44 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 108 4 9 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 44 108 (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 44 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 108 2 17 22 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 108 4 8 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 108 (accept_3_4 31 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  108 2 15 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 108 4 7 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 44 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 108 2 13 22 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 108 (accept_3_4 25 44 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 108 4 6 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 108 (Polychromatic418967fa.accept_13_10_5_4_1_3107 23 44 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 108 2 11 22 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 108
  (Polychromatic418967fa.accept_17_4_10_6_1_4869 21 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 108 4 5 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 108 (accept_3_4 19 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  108 2 9 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 108 (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 108 4 4 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 44 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 108 2 7 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 108 (accept_3_4 13 44 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 108 4 3 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 108 (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 44 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 108 2 5 22 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 108
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 108 4 2 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 108 (accept_3_4 7 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 108
  2 3 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  108 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 44 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 108 4 1 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 108 (Polychromatic418967fa.accept_23_3_21_16_1_4868 3 44 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 108 2 1 22 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 108 (accept_3_4 1 44 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 108)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 108 (allA_succ_of_accept 42 43
  108 (Polychromatic418967fa.accept_15_12_13_3_1_1915 42 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 43 108 (accept_3_5 41 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 43 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 43 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 108 (accept_3_5 38 43 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 37
  43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 108
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 108 (accept_3_5 35 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 108 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 108 (accept_3_5 32 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 43 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 108
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 108 (accept_3_5 29 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 108 (Polychromatic418967fa.accept_19_9_5_13_1_4867 28 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 108 (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 43 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 108 (accept_3_5 26 43 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 43 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 108
  (Polychromatic418967fa.accept_15_9_13_3_1_535 24 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 108 (accept_3_5 23 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 108 (Polychromatic418967fa.accept_29_22_14_21_1_4866 22 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 108 (accept_3_5 20 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 108
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 108 (accept_3_5 17 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 108 (accept_3_5 14 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 108 (Polychromatic418967fa.accept_20_13_3_8_1_4865 13 43 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 108
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 108 (accept_3_5 11 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 108 (Polychromatic418967fa.accept_15_10_13_3_1_4816 10 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 108 (accept_3_5 8 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 43 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 108
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 108 (accept_3_5 5 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  108 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 108 (Polychromatic418967fa.accept_17_3_9_6_1_3726 3 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 108 (accept_3_5 2 43 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 43 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 108))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 108
  (allA_succ_of_accept 41 42 108 (Polychromatic418967fa.accept_19_3_4_13_1_4864 41 42 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 108 2 20 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 108 3 13 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 108 2 19 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 108 (Polychromatic418967fa.accept_15_7_12_3_1_1137
  37 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 108 6 6 7 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 108
  (Polychromatic418967fa.accept_10_5_2_8_1_135 35 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 108 2 17 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 42 108 3 11 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 42 108 2 16 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 108 (Polychromatic418967fa.accept_17_14_8_6_1_2643 31 42 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 108 6 5 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 108 (Polychromatic418967fa.accept_16_13_10_12_1_1811 29 42
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 108 2 14 21 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 108 3 9 14 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 108 2 13 21 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 108
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 108 6 4 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 108 (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 42 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 108 2 11 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 108 3 7 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 108 2 10 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 108 (Polychromatic418967fa.accept_16_3_10_12_1_4814
  19 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 108 6 3 7 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 108
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 108 2 8 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 108 3 5 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 108 2 7 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 108 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 42 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 108 6 2 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 108 (Polychromatic418967fa.accept_16_11_10_12_1_4832 11 42
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 108 2 5 21 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 108 3 3 14 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 108 2 4 21 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 108
  (Polychromatic418967fa.accept_13_7_3_4_1_459 7 42 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 108 6 1 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 108 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 42 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 108 2 2 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 108 3 1 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 108 2 1 21 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 108 (Polychromatic418967fa.accept_13_1_3_4_1_925 1 42 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  108)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 108 (allA_succ_of_accept 40 41 108 (accept_3_4 40 41 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 39
  41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 108
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 38 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 108 (accept_3_4 37 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 108 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 108 (Polychromatic418967fa.accept_16_3_9_12_1_4831 35 41 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 108 (accept_3_4 34 41 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 108 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 41 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 108
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 108 (accept_3_4 31 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 108 (accept_3_4 28 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 108 (Polychromatic418967fa.accept_19_8_3_13_1_4863 27 41 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 108
  (Polychromatic418967fa.accept_19_7_3_13_1_3492 26 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 108 (accept_3_4 25 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 108 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 108 (accept_3_4 22 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 41 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 108
  (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 108 (accept_3_4 19 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 108 (Polychromatic418967fa.accept_14_3_13_10_1_761 17 41 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 108 (accept_3_4 16 41 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 108 (Polychromatic418967fa.accept_24_15_17_12_1_662 15 41
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 108
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 108 (accept_3_4 13 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 108 (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 108 (accept_3_4 10 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 108
  (Polychromatic418967fa.accept_15_8_11_3_1_3847 8 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 108 (accept_3_4 7 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  108 (Polychromatic418967fa.accept_13_6_2_4_1_923 6 41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 41 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 108 (accept_3_4 4 41 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 108 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 41 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  41 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 108 (accept_3_4 1 41 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 108))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 108
  (allA_succ_of_accept 39 40 108 (Polychromatic418967fa.accept_15_9_10_3_1_2845 39 40 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 108 2 19 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 37
  40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 108 4 9 10 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 108 (accept_3_5 35
  40 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 108 2 17 20 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 108
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 33 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 40 108 4 8 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 40 108 (Polychromatic418967fa.accept_13_5_1_4_1_3966 31 40 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 108 2 15 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 108 (accept_3_5 29 40 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 108 4 7 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 40 108 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 40 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 108 2 13 20 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 108
  (Polychromatic418967fa.accept_16_9_8_12_1_979 25 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 40 108 4 6 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 40 108 (accept_3_5 23 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40
  108 2 11 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  40 108 (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 40 108 4 5 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 40 108 (Polychromatic418967fa.accept_14_5_12_10_1_2985 19 40 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 108 2 9 20 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 108 (accept_3_5 17 40 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 108 4 4 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 40 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 40 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 108 2 7 20 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 108
  (Polychromatic418967fa.accept_11_2_7_9_1_890 13 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 108 4 3 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 108 (accept_3_5 11 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  108 2 5 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  40 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 40 108 4 2 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 40 108 (Polychromatic418967fa.accept_15_7_10_3_1_2891 7 40 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 108 2 3 20 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 108 (accept_3_5 5 40 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 108 4 1 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 40 108 (Polychromatic418967fa.accept_13_3_1_4_1_945 3 40 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 108 2 1 20 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 40 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 108)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 108 (allA_succ_of_accept 38 39 108
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 38 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 108 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 108 3 12 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 35
  39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 108
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 108 3 11 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 108 (Polychromatic418967fa.accept_21_11_18_3_1_4862 32 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 108 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 39 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 108 3 10 13 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 108
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 108 (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 108 3 9 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 108 (Polychromatic418967fa.accept_19_7_1_13_1_4861 26 39 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 108
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 108 3 8 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 108 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 39 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 108 3 7 13 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 108
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 108 3 6 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 108 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 39 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 108
  (Polychromatic418967fa.accept_19_16_1_13_1_4860 16 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 108 3 5 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 108 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 39 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 108 3 4 13 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 108
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 108 (Polychromatic418967fa.accept_15_10_9_3_1_1947 10 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 108 3 3 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 39 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 108
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 108 3 2 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 108 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 108 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 39 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 108 3 1 13 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 108
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 2 39 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 39 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 108))))))))))))))))))))))))))))))))))))))) (allB_succ 38 108
  (allA_succ_of_accept 37 38 108 (accept_3_4 37 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  108 2 18 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 108 (Polychromatic418967fa.accept_15_5_8_3_1_556 35 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 108 2 17 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 108 (Polychromatic418967fa.accept_13_7_12_4_1_450 33 38 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 108 2 16 19 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 108 (accept_3_4 31 38 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 108 2 15 19 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 108
  (Polychromatic418967fa.accept_11_7_5_9_1_884 29 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 108 2 14 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 108 (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 38 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 108 2 13 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 108 (accept_3_4 25 38 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 108 2 12 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 108 (Polychromatic418967fa.accept_20_3_18_8_1_4859 23 38 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 108 2 11 19 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 108
  (Polychromatic418967fa.accept_13_8_12_4_1_4858 21 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 108 2 10 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 108 (accept_3_4 19 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  108 2 9 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 108 (Polychromatic418967fa.accept_23_17_15_16_1_4857 17 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 108 2 8 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 108 (Polychromatic418967fa.accept_13_2_12_4_1_943 15 38 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 108 2 7 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 108 (accept_3_4 13 38 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 108 2 6 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 108 (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 38 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 108 2 5 19 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 108
  (Polychromatic418967fa.accept_15_9_8_3_1_557 9 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 108 2 4 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 108 (accept_3_4 7 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 108
  2 3 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  108 (Polychromatic418967fa.accept_13_5_12_4_1_449 5 38 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 38 108 2 2 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 38 108 (Polychromatic418967fa.accept_13_3_12_4_1_110 3 38 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 108 2 1 19 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 108 (accept_3_4 1 38 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 38 108)))))))))))))))))))))))))))))))))))))) (allB_succ 37 108 (allA_succ_of_accept 36
  37 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 37 108 (accept_3_5 35 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 37 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 37 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 108 (accept_3_5 32 37 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 108 (Polychromatic418967fa.accept_17_14_3_6_1_3716
  31 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 108
  (Polychromatic418967fa.accept_20_10_17_8_1_4856 30 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 108 (accept_3_5 29 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 108 (Polychromatic418967fa.accept_13_2_11_4_1_445 28 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 37 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 108 (accept_3_5 26 37 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 37 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 108
  (Polychromatic418967fa.accept_11_2_4_9_1_484 24 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 108 (accept_3_5 23 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 108 (Polychromatic418967fa.accept_13_8_11_4_1_1553 21 37 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 108 (accept_3_5 20 37 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 108
  (Polychromatic418967fa.accept_17_1_3_6_1_3672 18 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 108 (accept_3_5 17 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 108 (Polychromatic418967fa.accept_19_16_18_13_1_4855 16 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 37 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 108 (accept_3_5 14 37 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 108 (accept_3_5 11 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 108 (Polychromatic418967fa.accept_13_10_11_4_1_2248 10 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 37 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 108 (accept_3_5 8 37 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 108 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 37 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 108
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 108 (accept_3_5 5 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  108 (Polychromatic418967fa.accept_15_4_7_3_1_119 4 37 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 108 (Polychromatic418967fa.accept_24_3_13_12_1_4854 3 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 108 (accept_3_5 2 37 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 108))))))))))))))))))))))))))))))))))))) (allB_succ 36 108
  (allA_succ_of_accept 35 36 108 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 36 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 108 2 17 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 108 3 11 12 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 108 4 8 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 108 (Polychromatic418967fa.accept_13_5_10_4_1_1564
  31 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 108 6 5 6 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 108
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 29 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 108 4 7 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 108 9 3 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 108 2 13 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 108 12 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 108 2 11 18 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 108 3 7 12 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 108 4 5 9 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 108
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 108 18 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 108 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 36 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 108 4 4 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 108 3 5 12 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 108 2 7 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 108 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 36 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 108 12 1 3 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 108
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 108 2 5 18 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 36 108 9 1 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 36 108 4 2 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 108 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 36 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 108 6 1 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 108 4 1 9 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 108 3 1 12 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 108 2 1 18 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 108
  (Polychromatic418967fa.accept_13_1_10_4_1_954 1 36 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 108)))))))))))))))))))))))))))))))))))) (allB_succ 35 108 (allA_succ_of_accept 34 35 108 (accept_3_4 34
  35 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 108
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 35 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 108 (accept_3_4 31 35 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 108 (Polychromatic418967fa.accept_19_11_16_13_1_4853 30 35 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 108
  (Polychromatic418967fa.accept_11_7_2_9_1_480 29 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 108 (accept_3_4 28 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 108 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 108 (Polychromatic418967fa.accept_11_4_2_9_1_496 26 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 108 (accept_3_4 25 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 108 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 35 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 108
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 108 (accept_3_4 22 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 108 (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 108 (Polychromatic418967fa.accept_13_7_9_4_1_918 20 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 108 (accept_3_4 19 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 108 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 35 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 108
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 108 (accept_3_4 16 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 108 (Polychromatic418967fa.accept_19_14_16_13_1_3488 14 35 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 108 (accept_3_4 13 35 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 35 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 108
  (Polychromatic418967fa.accept_14_11_7_10_1_4852 11 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 108 (accept_3_4 10 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 108 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 108 (Polychromatic418967fa.accept_13_8_9_4_1_1552 8 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 108 (accept_3_4 7 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 108 (Polychromatic418967fa.accept_13_6_9_4_1_2288 6 35 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 108
  (Polychromatic418967fa.accept_13_5_9_4_1_441 5 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 108 (accept_3_4 4 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  108 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 35 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 35 108 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 108 (accept_3_4 1 35 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 35 108))))))))))))))))))))))))))))))))))) (allB_succ 34 108 (allA_succ_of_accept 33 34
  108 (Polychromatic418967fa.accept_16_1_2_12_1_1757 33 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 34 108 2 16 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 34 108 (Polychromatic418967fa.accept_14_3_6_10_1_752 31 34 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 108 2 15 17 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 108 (accept_3_5 29 34 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 108 2 14 17 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 108
  (Polychromatic418967fa.accept_21_6_13_3_1_4851 27 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 34 108 2 13 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 34 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 34 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 108 2 12 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 108 (accept_3_5 23 34 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 108 2 11 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 108 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 34 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 34 108 2 10 17 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 34 108
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 34 108 2 9 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 34 108 (accept_3_5 17 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34
  108 2 8 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  34 108 (Polychromatic418967fa.accept_16_15_2_12_1_1799 15 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 34 108 2 7 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 34 108 (Polychromatic418967fa.accept_20_13_14_8_1_4850 13 34 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 108 2 6 17 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 108 (accept_3_5 11 34 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 108 2 5 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 34 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 34 108 2 4 17 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 34 108
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 34 108 2 3 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 34 108 (accept_3_5 5 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 108
  2 2 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 34
  108 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 34 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 34 108 2 1 17 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 34 108 (Polychromatic418967fa.accept_15_1_4_3_1_1928 1 34 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 108)))))))))))))))))))))))))))))))))) (allB_succ 33 108
  (allA_succ_of_accept 32 33 108 (Polychromatic418967fa.accept_13_6_7_4_1_2264 32 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 33 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 108 3 10 11 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 108 (Polychromatic418967fa.accept_21_7_12_3_1_4849 28 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 108 3 9 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 108 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 33 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 108
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 33 108 3 8 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 33 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 33 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 108 3 7 11 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 108
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 20 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 108 (Polychromatic418967fa.accept_13_6_7_4_1_2264 19 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 108 3 6 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 108 (Polychromatic418967fa.accept_21_17_12_3_1_4848 17 33
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 108
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 33 108 3 5 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 33 108 (Polychromatic418967fa.accept_20_14_13_8_1_4847 14 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 33 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 108 3 4 11 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 108
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 108 (Polychromatic418967fa.accept_13_10_7_4_1_2262 10 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 108 3 3 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 33 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 108
  (Polychromatic418967fa.accept_17_7_16_6_1_3705 7 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 33 108 3 2 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 33 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 108 (Polychromatic418967fa.accept_16_4_1_12_1_1792 4 33 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 108 3 1 11 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 108
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 33 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 33 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 33 108))))))))))))))))))))))))))))))))) (allB_succ 32 108
  (allA_succ_of_accept 31 32 108 (accept_3_4 31 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  108 2 15 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  32 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 108 4 7 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 32 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 108 2 13 16 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 108 (accept_3_4 25 32 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 108 4 6 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 108 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 32 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 108 2 11 16 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 108
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 21 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 108 4 5 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 108 (accept_3_4 19 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  108 2 9 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 108 (Polychromatic418967fa.accept_22_17_10_20_1_4846 17 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 108 4 4 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 32 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 108 2 7 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 108 (accept_3_4 13 32 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 108 4 3 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 108 (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 32 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 108 2 5 16 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 108
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 108 4 2 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 108 (accept_3_4 7 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 108
  2 3 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  108 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 32 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 108 4 1 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 108 (Polychromatic418967fa.accept_22_3_10_20_1_4845 3 32 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 108 2 1 16 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 108 (accept_3_4 1 32 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 108)))))))))))))))))))))))))))))))) (allB_succ 31 108 (allA_succ_of_accept 30 31 108
  (Polychromatic418967fa.accept_19_11_12_13_1_4844 30 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 31 108 (accept_3_5 29 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 31 108 (Polychromatic418967fa.accept_13_2_5_4_1_3926 28 31 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 31 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 108 (accept_3_5 26 31 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 108 (Polychromatic418967fa.accept_13_12_5_4_1_3133
  25 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 108
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 108 (accept_3_5 23 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 108 (Polychromatic418967fa.accept_13_9_5_4_1_1591 22 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 108 (Polychromatic418967fa.accept_14_7_3_10_1_1364 21 31 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 108 (accept_3_5 20 31 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 31 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 108
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 108 (accept_3_5 17 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 108 (Polychromatic418967fa.accept_19_16_12_13_1_4843 16 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 108 (Polychromatic418967fa.accept_13_2_5_4_1_3926 15 31 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 108 (accept_3_5 14 31 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 108 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 31 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 108
  (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 108 (accept_3_5 11 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 108 (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 108 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 31 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 108 (accept_3_5 8 31 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 108 (Polychromatic418967fa.accept_14_7_3_10_1_1364 7 31 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 108
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 6 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 108 (accept_3_5 5 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  108 (Polychromatic418967fa.accept_15_4_1_3_1_1922 4 31 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 108 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 31 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 108 (accept_3_5 2 31 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 108 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 31 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 108))))))))))))))))))))))))))))))) (allB_succ 30 108
  (allA_succ_of_accept 29 30 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 30 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 108 2 14 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 108 3 9 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 108 2 13 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 108 (Polychromatic418967fa.accept_19_6_11_13_1_4842
  25 30 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 108 6 4 5 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 108
  (Polychromatic418967fa.accept_21_2_9_3_1_4841 23 30 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 108 2 11 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 30 108 3 7 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 108 2 10 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 108 6 3 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 108 (Polychromatic418967fa.accept_19_17_11_13_1_4840 17 30
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 108 2 8 15 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 108 3 5 10 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 108 2 7 15 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 108
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 30 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 108 6 2 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 108 (Polychromatic418967fa.accept_17_11_13_6_1_2625 11 30 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 108 2 5 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 108 3 3 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 108 2 4 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 108 (Polychromatic418967fa.accept_17_7_13_6_1_811 7 30 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 108 6 1 5 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 30 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 108 2 2 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 108 3 1 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 108 2 1 15 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 30 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 108)))))))))))))))))))))))))))))) (allB_succ 29 108 (allA_succ_of_accept
  28 29 108 (accept_3_4 28 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 108
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 108 (accept_3_4 25 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 108 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 29 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 23
  29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 108 (accept_3_4 22 29
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 108
  (Polychromatic418967fa.accept_10_1_9_8_1_123 21 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 108 (Polychromatic418967fa.accept_13_7_3_4_1_459 20 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 108 (accept_3_4 19 29 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 29 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 17
  29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 108 (accept_3_4 16 29
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 108
  (Polychromatic418967fa.accept_16_15_13_12_1_1787 15 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 108 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 29 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 108 (accept_3_4 13 29 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 108
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 108 (accept_3_4 10 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 108 (Polychromatic418967fa.accept_16_8_13_12_1_3809 8 29 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 108 (accept_3_4 7 29 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 108 (Polychromatic418967fa.accept_19_6_10_13_1_4839 6 29 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 108
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 108 (accept_3_4 4 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  108 (Polychromatic418967fa.accept_19_3_10_13_1_3482 3 29 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 29 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 29 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 108 (accept_3_4 1 29 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 29 108))))))))))))))))))))))))))))) (allB_succ 28 108 (allA_succ_of_accept 27 28 108
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 108 2 13 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 108 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 28 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 108 4 6 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 108 (accept_3_5 23 28 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 108 2 11 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 28 108 (Polychromatic418967fa.accept_17_4_11_6_1_3730 21 28 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 108 4 5 7 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 108
  (Polychromatic418967fa.accept_13_6_2_4_1_923 19 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 108 2 9 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 108 (accept_3_5 17 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  108 4 4 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 108 (Polychromatic418967fa.accept_19_15_9_13_1_4838 15 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 108 2 7 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 108 (Polychromatic418967fa.accept_17_13_11_6_1_4837 13 28 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 108 4 3 7 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 108 (accept_3_5 11 28 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 108 2 5 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 108 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 28 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 108 4 2 7 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 108
  (Polychromatic418967fa.accept_19_7_9_13_1_4836 7 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 108 2 3 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 108 (accept_3_5 5 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 108
  4 1 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 108
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 28 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 108 2 1 14 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 108 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 28 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 108)))))))))))))))))))))))))))) (allB_succ 27 108 (allA_succ_of_accept 26
  27 108 (Polychromatic418967fa.accept_16_10_11_12_1_4835 26 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 27 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 108 3 8 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  27 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 108
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 22 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 108 3 7 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 108 (Polychromatic418967fa.accept_16_4_11_12_1_1775 20 27 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 108 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 27 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 108 9 2 3 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 108
  (Polychromatic418967fa.accept_14_3_13_10_1_761 17 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 108 3 5 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 108 (Polychromatic418967fa.accept_19_14_8_13_1_4834 14 27
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 108
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 108 3 4 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 108 (Polychromatic418967fa.accept_13_10_1_4_1_3103 10 27
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 108 9 1 3 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 108
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 27 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 108 3 2 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 108 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 27 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 108
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 108 3 1 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 27 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 108 (Polychromatic418967fa.accept_16_1_11_12_1_1774 1 27 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 108))))))))))))))))))))))))))) (allB_succ 26
  108 (allA_succ_of_accept 25 26 108 (accept_3_4 25 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  26 108 2 12 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 108 2 11 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 108 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 26 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 108 2 10 13 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 108 (accept_3_4 19 26 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 108 2 9 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 108 (Polychromatic418967fa.accept_19_17_7_13_1_4833
  17 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 108 2 8 13 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 108 2 7 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 108 (accept_3_4 13 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  108 2 6 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 108 (Polychromatic418967fa.accept_16_11_10_12_1_4832 11 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 108 2 5 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 26 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 108 2 4 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 108 (accept_3_4 7 26 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 108 2 3 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 108 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 26 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 108 2 2 13 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 108
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 108 2 1 13 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 108 (accept_3_4 1 26 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  108)))))))))))))))))))))))))) (allB_succ 25 108 (allA_succ_of_accept 24 25 108
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 108 (accept_3_5 23 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 108 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 25 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 108 (accept_3_5 20 25 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 108 (Polychromatic418967fa.accept_16_3_9_12_1_4831 19 25 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 108
  (Polychromatic418967fa.accept_13_5_12_4_1_449 18 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 108 (accept_3_5 17 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 108 (Polychromatic418967fa.accept_13_3_12_4_1_110 16 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 25 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 108 (accept_3_5 14 25 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 108
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 108 (accept_3_5 11 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 108 (Polychromatic418967fa.accept_19_10_6_13_1_4830 10 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 108 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 25 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 108 (accept_3_5 8 25 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 108 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 25 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 108
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 108 (accept_3_5 5 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  108 (Polychromatic418967fa.accept_16_4_9_12_1_4829 4 25 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 25 108 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 25 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 108 (accept_3_5 2 25 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 108))))))))))))))))))))))))) (allB_succ 24 108
  (allA_succ_of_accept 23 24 108 (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 24 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 108 2 11 12 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 108 3 7 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 108 4 5 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 108 (Polychromatic418967fa.accept_10_9_4_8_1_741 19
  24 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 108 6 3 4 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 108
  (Polychromatic418967fa.accept_16_1_8_12_1_405 17 24 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 108 4 4 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 108 3 5 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 108 2 7 12 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 108 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 24 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 108 12 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 108 (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 24
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 108 2 5 12 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 108 3 3 8 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 108 4 2 6 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 108
  (Polychromatic418967fa.accept_11_7_2_9_1_480 7 24 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 108 6 1 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 108 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 24 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 108 4 1 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 108 3 1 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 108 2 1 12 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 108 (Polychromatic418967fa.accept_16_1_8_12_1_405 1 24 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 108)))))))))))))))))))))))) (allB_succ 23
  108 (allA_succ_of_accept 22 23 108 (accept_3_4 22 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 23 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 108 (accept_3_4 19 23 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 108 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 23 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 108
  (Polychromatic418967fa.accept_19_17_4_13_1_4828 17 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 108 (accept_3_4 16 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 108 (Polychromatic418967fa.accept_13_1_10_4_1_954 14 23 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 108 (accept_3_4 13 23 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 108 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 108
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 108 (accept_3_4 10 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 108 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 23 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 108 (accept_3_4 7 23 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 23 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 108 (accept_3_4 4 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  108 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 23 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 108 (Polychromatic418967fa.accept_16_2_7_12_1_3793 2 23 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 108 (accept_3_4 1 23 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 108))))))))))))))))))))))) (allB_succ 22 108 (allA_succ_of_accept 21 22 108
  (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 22 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 108 2 10 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 22 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 108 2 9 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 108 (accept_3_5 17 22 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 108 2 8 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 108 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 22 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 108 2 7 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 108 (Polychromatic418967fa.accept_25_13_22_8_1_4827
  13 22 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 108 2 6 11 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 108 (accept_3_5 11
  22 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 108 2 5 11 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 108
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 22 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 108 2 4 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 108 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 22 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 108 2 3 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 108 (accept_3_5 5 22 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 108 2 2 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 108 (Polychromatic418967fa.accept_17_3_5_6_1_4826 3 22 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 108 2 1 11 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 108 (Polychromatic418967fa.accept_17_1_5_6_1_3717 1
  22 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 108)))))))))))))))))))))) (allB_succ
  21 108 (allA_succ_of_accept 20 21 108 (Polychromatic418967fa.accept_15_5_6_3_1_525 20 21 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 108 (Polychromatic418967fa.accept_10_9_1_8_1_755
  19 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 108 3 6 7 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 108
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 108 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 21 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 108 3 5 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 108 (Polychromatic418967fa.accept_23_14_21_16_1_4825 14 21
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 108
  (Polychromatic418967fa.accept_10_3_1_8_1_132 13 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 108 3 4 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 108 (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 21 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 108 (Polychromatic418967fa.accept_13_10_8_4_1_3098 10 21
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 108 3 3 7 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 108
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 108 (Polychromatic418967fa.accept_16_7_5_12_1_4824 7 21 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 108 3 2 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 108 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 21 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 108
  (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 21 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 108 3 1 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 108 (Polychromatic418967fa.accept_17_2_4_6_1_1619 2 21 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 21 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 108))))))))))))))))))))) (allB_succ 20 108
  (allA_succ_of_accept 19 20 108 (accept_3_4 19 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20
  108 2 9 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  20 108 (Polychromatic418967fa.accept_14_3_6_10_1_752 17 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 20 108 4 4 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 20 108 (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 20 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 108 2 7 10 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 108 (accept_3_4 13 20 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 108 4 3 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20 108 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 20 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 108 2 5 10 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 108
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 108 4 2 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 108 (accept_3_4 7 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 108
  2 3 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  108 (Polychromatic418967fa.accept_16_5_4_12_1_3800 5 20 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 20 108 4 1 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 20 108 (Polychromatic418967fa.accept_13_3_7_4_1_435 3 20 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 108 2 1 10 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 108 (accept_3_4 1 20 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 20 108)))))))))))))))))))) (allB_succ 19 108 (allA_succ_of_accept 18 19 108
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 108 (accept_3_5 17 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 108 (accept_3_5 14 19 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 108 (Polychromatic418967fa.accept_17_13_2_6_1_3683 13 19 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 108
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 108 (accept_3_5 11 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 108 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 19 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 108 (accept_3_5 8 19 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 108 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 19 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 108
  (Polychromatic418967fa.accept_21_6_19_3_1_4823 6 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 108 (accept_3_5 5 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  108 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 19 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 108 (Polychromatic418967fa.accept_22_3_19_20_1_4822 3 19 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 108 (accept_3_5 2 19 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 108 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 108))))))))))))))))))) (allB_succ 18 108 (allA_succ_of_accept 17
  18 108 (Polychromatic418967fa.accept_16_1_2_12_1_1757 17 18 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 18 108 2 8 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 18 108 3 5 6 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 18 108 2 7 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 108 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 18 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 108 6 2 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 108 (Polychromatic418967fa.accept_20_11_18_8_1_4821
  11 18 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 108 2 5 9 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 18 108 9 1 2 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 18 108 2 4 9 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 108
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 18 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 108 6 1 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 108 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 18 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 108 2 2 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 108 3 1 6 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 108 2 1 9 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 18 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 108)))))))))))))))))) (allB_succ 17 108
  (allA_succ_of_accept 16 17 108 (accept_3_4 16 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 108 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 108 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 17 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 108 (accept_3_4 13 17 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 108 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 17 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 108
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 11 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 108 (accept_3_4 10 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 108 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 108 (Polychromatic418967fa.accept_16_8_1_12_1_984 8 17 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 108 (accept_3_4 7 17 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 108 (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 17 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 108
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 108 (accept_3_4 4 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  108 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 17 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 17 108 (Polychromatic418967fa.accept_16_2_1_12_1_3798 2 17 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 108 (accept_3_4 1 17 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 17 108))))))))))))))))) (allB_succ 16 108 (allA_succ_of_accept 15 16 108
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 108 2 7 8 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 108 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 108 4 3 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 108 (accept_3_5 11 16 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 108 2 5 8 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 108 (Polychromatic418967fa.accept_17_9_16_6_1_4820 9 16 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 108 4 2 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 108 (Polychromatic418967fa.accept_11_7_5_9_1_884 7
  16 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 108 2 3 8 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 108 (accept_3_5 5 16
  108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 108 4 1 4 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 108
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 16 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 108 2 1 8 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 16 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 108)))))))))))))))) (allB_succ 15 108 (allA_succ_of_accept 14 15 108
  (Polychromatic418967fa.accept_17_14_15_6_1_4819 14 15 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 108 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 15 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 108 3 4 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 15 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 108
  (Polychromatic418967fa.accept_20_10_15_8_1_4818 10 15 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 108 3 3 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 108 (Polychromatic418967fa.accept_16_8_15_12_1_1747 8 15 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 108 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 15 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 108 3 2 5 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 108
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 15 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 108 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 108 3 1 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 108 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 15 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 108
  (Polychromatic418967fa.accept_21_1_15_3_1_4817 1 15 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 108))))))))))))))) (allB_succ 14 108 (allA_succ_of_accept 13 14 108 (accept_3_4 13 14 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 108 2 6 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 108 (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 14
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 108 2 5 7 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 108
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 14 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 108 2 4 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 108 (accept_3_4 7 14 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 108
  2 3 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 108
  (Polychromatic418967fa.accept_13_5_1_4_1_3966 5 14 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 108 2 2 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 108 (Polychromatic418967fa.accept_13_3_1_4_1_945 3 14 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 108 2 1 7 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 108 (accept_3_4 1 14 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 108)))))))))))))) (allB_succ 13 108 (allA_succ_of_accept 12 13 108
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 108 (accept_3_5 11 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 108 (Polychromatic418967fa.accept_15_10_13_3_1_4816 10 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 108 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 108 (accept_3_5 8 13 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 108 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 13 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 108
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 108 (accept_3_5 5 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  108 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 108 (Polychromatic418967fa.accept_14_3_13_10_1_761 3 13 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 108 (accept_3_5 2 13 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 108 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 13 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 108))))))))))))) (allB_succ 12 108 (allA_succ_of_accept 11 12
  108 (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 12 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 12 108 2 5 6 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 12 108 3 3 4 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 12 108 4 2 3 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 12 108 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 12 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 108 6 1 2 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 108 (Polychromatic418967fa.accept_10_5_2_8_1_135 5
  12 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 108 4 1 3 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 108 3 1 4 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 108 2 1 6 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 108
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 108)))))))))))) (allB_succ 11 108 (allA_succ_of_accept 10 11 108 (accept_3_4 10 11 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 108 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 11 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 108
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 11 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 108 (accept_3_4 7 11 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  108 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 11 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 108 (Polychromatic418967fa.accept_17_5_11_6_1_4815 5 11 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 108 (accept_3_4 4 11 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 108 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 11 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 108 (Polychromatic418967fa.accept_13_2_11_4_1_445 2
  11 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 108 (accept_3_4 1 11 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 108))))))))))) (allB_succ 10 108 (allA_succ_of_accept 9 10 108
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 10 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 108 2 4 5 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 108 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 10 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 108 2 3 5 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 108 (accept_3_5 5 10 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 108 2 2 5 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 108 (Polychromatic418967fa.accept_16_3_10_12_1_4814 3 10 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 108 2 1 5 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 108 (Polychromatic418967fa.accept_11_1_10_9_1_871 1
  10 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 108)))))))))) (allB_succ 9 108
  (allA_succ_of_accept 8 9 108 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 9 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 108 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 9 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 108 3 2 3 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 108
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 108 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 9 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 108 3 1 3 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 108 (Polychromatic418967fa.accept_16_2_9_12_1_46 2 9 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 108
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 108))))))))) (allB_succ 8 108 (allA_succ_of_accept 7 8 108 (accept_3_4 7 8 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 108 2 3 4 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 8 108 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 8 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 108 4 1 2 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 108
  (Polychromatic418967fa.accept_16_3_8_12_1_2736 3 8 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 8 108 2 1 4 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 8 108 (accept_3_4 1 8 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 108))))))))
  (allB_succ 7 108 (allA_succ_of_accept 6 7 108 (Polychromatic418967fa.accept_13_6_7_4_1_2264 6 7 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 108 (accept_3_5 5 7 108 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 108 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 7 108
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 108
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 7 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 7 108 (accept_3_5 2 7 108 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 108
  (Polychromatic418967fa.accept_19_1_7_13_1_4813 1 7 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 7 108))))))) (allB_succ 6 108 (allA_succ_of_accept 5 6 108 (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 6
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 108 2 2 3 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 6 108 3 1 2 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 6 108 2 1 3 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 108
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 6 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 108)))))) (allB_succ 5 108 (allA_succ_of_accept 4 5 108 (accept_3_4 4 5 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 108 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 5 108 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 108 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 5
  108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 108 (accept_3_4 1 5 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 108))))) (allB_succ 4 108 (allA_succ_of_accept 3 4 108
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 4 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 4 108 2 1 2 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 4 108 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 4 108)))) (allB_succ 3 108 (allA_succ_of_accept 2 3 108
  (Polychromatic418967fa.accept_22_2_3_20_1_4812 2 3 108 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 108 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 3 108 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 108))) (allB_succ 2 108 (allA_succ_of_accept 1 2 108 (accept_3_4 1 2 108
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 108)) (allB_two
  108))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


