-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch152
-- name    : Polychromatic418967fa_Branch152
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:16:44.033203+00:00
-- url     : https://prove2.me/theorems/71a0f694-2e0b-489c-afa1-4da0a7a2c4d9
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

def Polychromatic418967fa.branch_152 : allB 152 152 :=
  allB_succ' 2 151 152 (Eq.refl Bool.true) (allA_of_3_0 2 151 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  150 152 (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 152 2 1 75 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 152 (accept_3_2 1 150 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 150 152))) (allB_succ' 4 149 152 (Eq.refl Bool.true) (allA_succ_of_accept 3 149 152
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 149 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 149 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 149 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 152 (accept_3_2 1 149 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 149 152)))) (allB_succ' 5 148 152 (Eq.refl Bool.true) (allA_of_3_0 5 148 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 147 152 (Eq.refl Bool.true) (allA_succ_of_accept 5 147 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 147 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 152 (accept_3_2 4 147 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 152 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 147 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 147 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 152 (accept_3_2 1 147 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 152)))))) (allB_succ' 7 146 152 (Eq.refl Bool.true) (allA_succ_of_gcd 6 146 152 2 3
  73 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 146 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 146 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 146 152 2 2 73 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 146 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 146 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 152 2 1 73 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 152 (accept_3_2 1 146 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 146 152))))))) (allB_succ' 8 145 152 (Eq.refl Bool.true) (allA_of_3_0 8 145 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 144 152 (Eq.refl Bool.true) (allA_succ_of_gcd 8 144 152 8 1 18 19
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 152
  (accept_3_2 7 144 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 152 2 3 72 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 152
  (Polychromatic418967fa.accept_13_5_1_9_1_618 5 144 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 144 152 4 1 36 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 144 152 (Polychromatic418967fa.accept_21_3_18_5_1_8211 3 144 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 152 2 1 72 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 152 (accept_3_2 1 144 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 152))))))))) (allB_succ' 10 143 152 (Eq.refl Bool.true) (allA_succ_of_accept 9 143 152
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 143 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 143 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 143 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 152 (accept_3_2 7 143 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 143 152 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 143 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 152 (Polychromatic418967fa.accept_10_5_3_2_1_899 5
  143 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 152 (accept_3_2 4 143
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 152 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 143 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 143 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 152 (accept_3_2 1 143 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  152)))))))))) (allB_succ' 11 142 152 (Eq.refl Bool.true) (allA_of_3_0 11 142 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 141 152 (Eq.refl Bool.true) (allA_succ_of_accept 11 141 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 141 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 152 (accept_3_2 10 141 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 152 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 141 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 152 (Polychromatic418967fa.accept_13_8_11_9_1_593 8 141 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 152 (accept_3_2 7 141 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 141 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 152 (accept_3_2 4 141 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 141 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 141 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 152 (accept_3_2 1 141 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 152)))))))))))) (allB_succ' 13 140 152 (Eq.refl Bool.true) (allA_succ_of_gcd 12 140
  152 4 3 35 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  140 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 140 152 2 5 70 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 140 152 (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 140 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 152 4 2 35 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 152 (accept_3_2 7 140 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140 152 2 3 70 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 140 152 (Polychromatic418967fa.accept_16_5_12_8_1_2521 5 140 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 152 4 1 35 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 152
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 140 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 140 152 2 1 70 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 140 152 (accept_3_2 1 140 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  152))))))))))))) (allB_succ' 14 139 152 (Eq.refl Bool.true) (allA_of_3_0 14 139 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 138 152 (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 152 2 7 69 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 152 (accept_3_2 13 138 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 152 2 6 69 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 138 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 152 2 5 69 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 138 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 138 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 152 2 4 69 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 152 (accept_3_2 7 138 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 138 152 2 3 69 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 138 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 138 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 152 2 2 69 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 138 152 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3
  138 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 152 2 1 69 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 152 (accept_3_2 1
  138 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 152))))))))))))))) (allB_succ' 16 137 152 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 137 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 137 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 152 (Polychromatic418967fa.accept_9_5_2_8_1_109
  14 137 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 152 (accept_3_2 13
  137 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 152
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 137 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 137 152 (Polychromatic418967fa.accept_13_11_7_9_1_612 11 137 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 152 (accept_3_2 10 137 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 137 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 8
  137 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 152 (accept_3_2 7 137
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 152
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 137 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 137 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 137 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 152 (accept_3_2 4 137 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 137 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  137 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 152 (accept_3_2 1 137
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137 152)))))))))))))))) (allB_succ' 17 136 152 (Eq.refl
  Bool.true) (allA_of_3_0 17 136 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 135 152 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 135 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 135 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 152 (accept_3_2 16 135 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 152 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 135 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 152
  (Polychromatic418967fa.accept_13_1_5_9_1_226 14 135 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 152 (accept_3_2 13 135 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 152 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 135 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 152 (accept_3_2 10 135 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 152 (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 135 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 152
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 135 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 152 (accept_3_2 7 135 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 152 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 135 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 135 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 152 (accept_3_2 4 135 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 135 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 152
  (Polychromatic418967fa.accept_13_2_5_9_1_610 2 135 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 152 (accept_3_2 1 135 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  152)))))))))))))))))) (allB_succ' 19 134 152 (Eq.refl Bool.true) (allA_succ_of_gcd 18 134 152 2 9 67 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 134 152
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 134 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 134 152 2 8 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 134 152 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 134 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 152 2 7 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 152 (accept_3_2 13 134 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 152 2 6 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 134 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 152 2 5 67 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 152
  (Polychromatic418967fa.accept_24_9_14_8_1_6401 9 134 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 152 2 4 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 152 (accept_3_2 7 134 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  152 2 3 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 134 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 152 2 2 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 134 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 134 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 152 2 1 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 152 (accept_3_2 1 134 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 134 152))))))))))))))))))) (allB_succ' 20 133 152 (Eq.refl Bool.true) (allA_of_3_0 20
  133 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 132 152 (Eq.refl Bool.true) (allA_succ_of_gcd 20 132
  152 4 5 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  132 152 (accept_3_2 19 132 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 152 2 9 66 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 152
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 17 132 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 152 4 4 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 132 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 132 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 152 2 7 66 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 152 (accept_3_2 13 132 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 152 4 3 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 132 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 152 2 5 66 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 152
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 132 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 152 4 2 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 152 (accept_3_2 7 132 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132
  152 2 3 66 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  132 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 132 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 152 4 1 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 132 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 152 2 1 66 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 152 (accept_3_2 1 132 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 132 152))))))))))))))))))))) (allB_succ' 22 131 152 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 131 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 131 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 131 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 152 (accept_3_2 19 131 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 152 (Polychromatic418967fa.accept_13_5_1_9_1_618
  18 131 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 152
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 17 131 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 152 (accept_3_2 16 131 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 131 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 152 (accept_3_2 13 131 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 152
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 131 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 152 (accept_3_2 10 131 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 152 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 131 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 152 (accept_3_2 7 131 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 152 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 131 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 152
  (Polychromatic418967fa.accept_13_5_1_9_1_618 5 131 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 152 (accept_3_2 4 131 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 131 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 152 (accept_3_2 1 131 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 152)))))))))))))))))))))) (allB_succ' 23 130 152 (Eq.refl Bool.true) (allA_of_3_0
  23 130 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 129 152 (Eq.refl Bool.true) (allA_succ_of_accept 23
  129 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 129 152 (accept_3_2 22 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 129 152 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 129 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 129 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 152 (accept_3_2 19 129 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 152 (Polychromatic418967fa.accept_12_6_9_8_1_165
  18 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 152 (accept_3_2 16 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 129 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 152 (accept_3_2 13 129 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 152 (Polychromatic418967fa.accept_16_12_1_8_1_5767 12 129 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 152 (accept_3_2 10 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 129 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 152 (accept_3_2 7 129 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 129 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 152 (accept_3_2 4 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 152 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 129 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 129 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 152 (accept_3_2 1 129 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 152)))))))))))))))))))))))) (allB_succ' 25 128 152 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 128 152 8 3 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 128 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 128 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 152 2 11 64 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 21
  128 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 128 152 4 5 32 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 128 152 (accept_3_2 19
  128 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 128 152 2 9 64 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 128 152
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 128 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 128 152 8 2 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 128 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 128 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 152 2 7 64 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 152 (accept_3_2 13 128 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 152 4 3 32 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 128 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 152 2 5 64 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 152
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 128 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 152 8 1 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 152 (accept_3_2 7 128 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  152 2 3 64 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 128 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 152 4 1 32 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 128 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 128 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 152 2 1 64 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 152 (accept_3_2 1 128 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128 152))))))))))))))))))))))))) (allB_succ' 26 127 152 (Eq.refl Bool.true)
  (allA_of_3_0 26 127 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 126 152 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 126 152 2 13 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 152 (accept_3_2 25 126 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 152 2 12 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 152 (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 126 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 152 2 11 63 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 152
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 126 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 152 2 10 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 152 (accept_3_2 19 126 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 152 2 9 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 152 (Polychromatic418967fa.accept_20_17_6_12_1_8185 17 126 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 152 2 8 63 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 126 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 152 2 7 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 126 152 (accept_3_2 13 126 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  126 152 2 6 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 126 152 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 126 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 126 152 2 5 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 126 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 126 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 152 2 4 63 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 152 (accept_3_2 7 126 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 152 2 3 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 152 (Polychromatic418967fa.accept_20_5_6_12_1_2444 5 126 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 152 2 2 63 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 126 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 126 152 2 1 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 126 152 (accept_3_2 1 126 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  152))))))))))))))))))))))))))) (allB_succ' 28 125 152 (Eq.refl Bool.true) (allA_succ_of_accept 27 125 152
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 125 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 125 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 152 (accept_3_2 25 125 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 125 152 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 125 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 152
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 152 (accept_3_2 22 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 152 (Polychromatic418967fa.accept_13_7_8_9_1_1158 20 125 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 152 (accept_3_2 19 125 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 125 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 152
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 152 (accept_3_2 16 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 125 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 152 (accept_3_2 13 125 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 152 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 125
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 152
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 152 (accept_3_2 10 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 125 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 152 (accept_3_2 7 125 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 152 (Polychromatic418967fa.accept_14_6_13_12_1_810 6 125 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 152
  (Polychromatic418967fa.accept_16_5_13_8_1_2454 5 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 152 (accept_3_2 4 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 152 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 125 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 152 (accept_3_2 1 125 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125 152)))))))))))))))))))))))))))) (allB_succ' 29 124 152 (Eq.refl Bool.true)
  (allA_of_3_0 29 124 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 123 152 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 123 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 123 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 152 (accept_3_2 28 123 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 123 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 152 (Polychromatic418967fa.accept_11_4_2_9_1_496
  26 123 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 152 (accept_3_2 25
  123 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 152
  (Polychromatic418967fa.accept_21_3_18_5_1_8211 24 123 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 152 (accept_3_2 22 123 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 123 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 152 (Polychromatic418967fa.accept_7_6_4_5_1_314
  20 123 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 152 (accept_3_2 19
  123 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 152
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 123 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 152 (accept_3_2 16 123 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 123 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 152 (Polychromatic418967fa.accept_9_5_6_8_1_101
  14 123 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 152 (accept_3_2 13
  123 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 152
  (Polychromatic418967fa.accept_9_3_6_8_1_308 12 123 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 152 (accept_3_2 10 123 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 123 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 8
  123 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 152 (accept_3_2 7 123
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 152
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 123 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 152 (accept_3_2 4 123 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 123 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  123 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 152 (accept_3_2 1 123
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 152)))))))))))))))))))))))))))))) (allB_succ' 31 122 152
  (Eq.refl Bool.true) (allA_succ_of_gcd 30 122 152 2 15 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 122 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 122 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 152 2 14 61 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 152
  (Polychromatic418967fa.accept_13_1_5_9_1_226 27 122 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 152 2 13 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 152 (accept_3_2 25 122 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 152 2 12 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 122 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 152 2 11 61 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 152
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 122 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 152 2 10 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 152 (accept_3_2 19 122 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 152 2 9 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 122 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 152 2 8 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  122 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 152 2 7 61 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 152 (accept_3_2 13
  122 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 152 2 6 61 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 152
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 122 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 152 2 5 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 122 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 152 2 4 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 152 (accept_3_2 7 122 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 152 2 3 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 122 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 152 2 2 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 3
  122 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 152 2 1 61 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 152 (accept_3_2 1
  122 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122 152))))))))))))))))))))))))))))))) (allB_succ' 32 121
  152 (Eq.refl Bool.true) (allA_of_3_0 32 121 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 120 152
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 152 8 4 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 120 152 (accept_3_2 31 120 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 152 2 15 60 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 152 4 7 30 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 152
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 120 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 120 152 2 13 60 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 120 152 (accept_3_2 25 120 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 152 8 3 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 120 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 152 2 11 60 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 152 (Polychromatic418967fa.accept_13_8_3_9_1_5269
  21 120 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 152 4 5 30 38
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 152
  (accept_3_2 19 120 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 152 2 9 60 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 152
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 120 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 152 8 2 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 120 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 120 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 152 2 7 60 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 152 (accept_3_2 13 120 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 152 4 3 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 120 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 152 2 5 60 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 152
  (Polychromatic418967fa.accept_21_9_15_5_1_3500 9 120 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 152 8 1 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 152 (accept_3_2 7 120 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120
  152 2 3 60 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  120 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 120 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 152 4 1 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 120 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 152 2 1 60 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 152 (accept_3_2 1 120 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 120 152))))))))))))))))))))))))))))))))) (allB_succ' 34 119 152 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 119 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 119 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 152 (accept_3_2 31 119 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 152 (Polychromatic418967fa.accept_9_3_2_8_1_108
  30 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 152
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 152 (accept_3_2 28 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 119 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 152 (accept_3_2 25 119 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 152 (accept_3_2 22 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 152 (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 119 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 152 (accept_3_2 19 119 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 152 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 119
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 152
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 152 (accept_3_2 16 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 119 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 152 (accept_3_2 13 119 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 152
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 152 (accept_3_2 10 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 152 (Polychromatic418967fa.accept_21_8_14_5_1_8177 8 119 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 152 (accept_3_2 7 119 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 119 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 152 (accept_3_2 4 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 119 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 152 (accept_3_2 1 119 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119 152)))))))))))))))))))))))))))))))))) (allB_succ' 35 118 152 (Eq.refl Bool.true)
  (allA_of_3_0 35 118 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 117 152 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 117 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 152 (accept_3_2 34 117 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 152 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 117 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 152
  (Polychromatic418967fa.accept_21_11_12_5_1_2224 32 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 117 152 (accept_3_2 31 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 117 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 117 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 152 (accept_3_2 28 117 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 152 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  27 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 152
  (Polychromatic418967fa.accept_20_6_17_12_1_8210 26 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 117 152 (accept_3_2 25 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 117 152 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 117 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 152 (accept_3_2 22 117 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 152
  (Polychromatic418967fa.accept_14_7_5_12_1_1439 21 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 117 152 (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 117 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 152 (accept_3_2 19 117 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 117 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 117 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 152 (accept_3_2 16 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 152 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 152 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 117 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 152 (accept_3_2 13 117 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 152 (Polychromatic418967fa.accept_16_12_5_8_1_2492 12 117
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 152 (accept_3_2 10 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 152 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 152 (Polychromatic418967fa.accept_21_8_12_5_1_8209 8 117 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 152 (accept_3_2 7 117 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 117 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 152 (accept_3_2 4 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 152 (Polychromatic418967fa.accept_14_3_5_12_1_4000 3 117 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 152 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 117 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 152 (accept_3_2 1 117 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117 152)))))))))))))))))))))))))))))))))))) (allB_succ' 37 116 152 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 116 152 4 9 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 152 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 116 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 152 2 17 58 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 152 (Polychromatic418967fa.accept_16_1_4_8_1_3434
  33 116 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 152 4 8 29 38
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 152
  (accept_3_2 31 116 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 152 2 15 58 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 116 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 152 4 7 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 116 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 152 2 13 58 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 152 (accept_3_2 25 116 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 152 4 6 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 116 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 152 2 11 58 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 152
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 116 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 152 4 5 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 152 (accept_3_2 19 116 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 152 2 9 58 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 116 152 (Polychromatic418967fa.accept_16_1_4_8_1_3434 17 116 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 116 152 4 4 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 116 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 116 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 152 2 7 58 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 152 (accept_3_2 13 116 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 152 4 3 29 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 152
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 116 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 152 2 5 58 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 116 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 116 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 152 4 2 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 152 (accept_3_2 7 116 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 116 152 2 3 58 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 116 152 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 116 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 152 4 1 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 152 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3
  116 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 152 2 1 58 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 152 (accept_3_2 1
  116 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116 152))))))))))))))))))))))))))))))))))))) (allB_succ' 38
  115 152 (Eq.refl Bool.true) (allA_of_3_0 38 115 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 114 152
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 152 38 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 114 152 (accept_3_2 37 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 152 2 18 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 152 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 114 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 152 2 17 57 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 152
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 152 2 16 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 152 (accept_3_2 31 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 152 2 15 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 114 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 152 2 14 57 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 152
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 152 2 13 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 152 (accept_3_2 25 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 152 2 12 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 114 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 152 2 11 57 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 152
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 152 2 10 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 19 114 152 19 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 114 152 2 9 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 114 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 152 2 8 57 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 152 2 7 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 114 152 (accept_3_2 13 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  114 152 2 6 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 114 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 114 152 2 5 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 114 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 114 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 152 2 4 57 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 152 (accept_3_2 7 114 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 152 2 3 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 114 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 152 2 2 57 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 114 152
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 114 152 2 1 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 114 152 (accept_3_2 1 114 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  152))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 113 152 (Eq.refl Bool.true) (allA_succ_of_accept 39 113 152
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 113 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 113 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 152 (accept_3_2 37 113 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 113 152 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 113 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 152
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 152 (accept_3_2 34 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 113 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 152 (accept_3_2 31 113 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 113 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 152
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 152 (accept_3_2 28 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 113 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 152 (accept_3_2 25 113 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 113 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 152
  (Polychromatic418967fa.accept_16_7_1_8_1_5796 23 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 152 (accept_3_2 22 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 113 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 152 (accept_3_2 19 113 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 113 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 152
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 152 (accept_3_2 16 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 113 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 152 (accept_3_2 13 113 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 113 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 152
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 152 (accept_3_2 10 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 152 (Polychromatic418967fa.accept_22_8_3_20_1_8170 8 113 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 152 (accept_3_2 7 113 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 113 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 152
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 152 (accept_3_2 4 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 113 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 152 (accept_3_2 1 113 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 152)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 112 152 (Eq.refl
  Bool.true) (allA_of_3_0 41 112 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 111 152 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 111 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 152 (accept_3_2 40 111 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 111 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 152 (Polychromatic418967fa.accept_9_2_3_8_1_318
  38 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 152 (accept_3_2 37
  111 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 152
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 152 (accept_3_2 34 111 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 111 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 152 (Polychromatic418967fa.accept_7_4_6_5_1_141
  32 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 152 (accept_3_2 31
  111 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 152
  (Polychromatic418967fa.accept_12_6_3_8_1_512 30 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 152 (accept_3_2 28 111 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 152 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 111 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 152
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 152 (accept_3_2 25 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 152 (accept_3_2 22 111 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 152 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 111 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 152 (accept_3_2 19 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 152 (accept_3_2 16 111 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 152 (accept_3_2 13 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 152 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 152 (accept_3_2 10 111 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 152 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 111 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 152
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 152 (accept_3_2 7 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 152 (accept_3_2 4 111 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 152 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 111 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 152 (accept_3_2 1 111 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  152)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 110 152 (Eq.refl Bool.true) (allA_succ_of_gcd 42 110 152
  2 21 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 110
  152 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 110 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 110 152 2 20 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 110 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 110 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 110 152 2 19 55 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 110 152 (accept_3_2 37 110 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 110 152 2 18 55 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 110 152
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 110 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 110 152 2 17 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 110 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 110 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 110 152 2 16 55 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 110 152 (accept_3_2 31 110 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 110 152 2 15 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 110 152 (Polychromatic418967fa.accept_12_5_2_8_1_172
  29 110 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 152 2 14 55 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 152
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 110 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 152 2 13 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 152 (accept_3_2 25 110 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 152 2 12 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 110 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 152 2 11 55 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 152
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 110 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 152 2 10 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 152 (accept_3_2 19 110 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 152 2 9 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 110 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 152 2 8 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  110 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 152 2 7 55 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 152 (accept_3_2 13
  110 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 152 2 6 55 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 152
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 110 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 152 2 5 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 152 (Polychromatic418967fa.accept_17_9_8_16_1_2176 9 110 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 152 2 4 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 152 (accept_3_2 7 110 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 152 2 3 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 110 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 152 2 2 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  110 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 152 2 1 55 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 152 (accept_3_2 1
  110 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110 152)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 109 152 (Eq.refl Bool.true) (allA_of_3_0 44 109 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 45 108 152 (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 152 4 11 27 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 152 (accept_3_2 43 108 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 108 152 2 21 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 108 152 (Polychromatic418967fa.accept_16_9_12_8_1_1554
  41 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 152 4 10 27 38
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 152
  (Polychromatic418967fa.accept_16_7_12_8_1_2450 39 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 152 2 19 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 152 (accept_3_2 37 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 152 4 9 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 108 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 152 2 17 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 152 (Polychromatic418967fa.accept_13_7_4_9_1_1865
  33 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 152 4 8 27 38
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 152
  (accept_3_2 31 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 152 2 15 54 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 152 4 7 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 152 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 108 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 152 2 13 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 152 (accept_3_2 25 108 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 152 4 6 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 108 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 152 2 11 54 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 152
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 21 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 152 4 5 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 108 152 (accept_3_2 19 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  108 152 2 9 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 108 152 (Polychromatic418967fa.accept_16_1_12_8_1_2405 17 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 108 152 4 4 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 108 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 152 2 7 54 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 152 (accept_3_2 13 108 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 152 4 3 27 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 152
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 11 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 152 2 5 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 108 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 152 4 2 27 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 152 (accept_3_2 7 108 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 152 2 3 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 108 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 152 4 1 27 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 152
  (Polychromatic418967fa.accept_16_3_12_8_1_808 3 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 152 2 1 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 152 (accept_3_2 1 108 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  152))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 107 152 (Eq.refl Bool.true) (allA_succ_of_accept 45
  107 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 152 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 107 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 152 (accept_3_2 43 107 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 152 (Polychromatic418967fa.accept_20_2_7_12_1_5215 42 107
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 152
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 41 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 152 (accept_3_2 40 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 107 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 152 (accept_3_2 37 107 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 152 (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 107 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 152
  (Polychromatic418967fa.accept_10_5_7_2_1_516 35 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 152 (accept_3_2 34 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 107 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 152 (accept_3_2 31 107 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 152 (Polychromatic418967fa.accept_22_8_19_20_1_8208 30 107 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 152
  (Polychromatic418967fa.accept_10_9_7_2_1_887 29 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 152 (accept_3_2 28 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 107 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 152 (accept_3_2 25 107 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 107 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 152
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 152 (accept_3_2 22 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 152 (Polychromatic418967fa.accept_13_7_3_9_1_1142 20 107 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 152 (accept_3_2 19 107 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 107 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 152
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 152 (accept_3_2 16 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 152 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 107 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 152 (accept_3_2 13 107 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 152 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 107
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 152
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 152 (accept_3_2 10 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 152 (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 107 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 152 (accept_3_2 7 107 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 152 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 107 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 152
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 152 (accept_3_2 4 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 107 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 152 (accept_3_2 1 107 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 152)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 106 152 (Eq.refl
  Bool.true) (allA_of_3_0 47 106 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 105 152 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 105 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 152 (accept_3_2 46 105 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 152 (Polychromatic418967fa.accept_13_6_1_9_1_619 45 105 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 152
  (Polychromatic418967fa.accept_13_5_1_9_1_618 44 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 152 (accept_3_2 43 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 152 (accept_3_2 40 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 105 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 152 (accept_3_2 37 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 152 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 152 (accept_3_2 34 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 152 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 105 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 152 (accept_3_2 31 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 152 (accept_3_2 28 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 152 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 105 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 152
  (Polychromatic418967fa.accept_20_6_5_12_1_8169 26 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 152 (accept_3_2 25 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 152 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 152 (accept_3_2 22 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 105 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 152 (accept_3_2 19 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 152 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 152 (accept_3_2 16 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 152 (Polychromatic418967fa.accept_13_2_1_9_1_1174 15 105 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 152 (accept_3_2 13 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 152 (accept_3_2 10 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 152 (Polychromatic418967fa.accept_14_9_7_12_1_4034 9 105 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 152
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 152 (accept_3_2 7 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 152 (accept_3_2 4 105 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 152 (accept_3_2 1 105 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  152)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 104 152 (Eq.refl Bool.true) (allA_succ_of_gcd 48
  104 152 8 6 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  47 104 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 104 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 104 152 2 23 52 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 104 152 (Polychromatic418967fa.accept_25_20_4_2_1_8207 45 104 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 104 152 4 11 26 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 104 152 (accept_3_2 43 104 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 104 152 2 21 52 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 104 152
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 41 104 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 104 152 8 5 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 104 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 104 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 104 152 2 19 52 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 104 152 (accept_3_2 37 104 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 104 152 4 9 26 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 104 152
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 104 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 104 152 2 17 52 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 104 152 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 104 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 152 8 4 13 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 152 (accept_3_2 31 104 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 152 2 15 52 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 29
  104 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 152 4 7 26 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 152
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 104 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 152 2 13 52 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 152 (accept_3_2 25 104 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 152 8 3 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 104 152 (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 104 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 152 2 11 52 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 21
  104 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 104 152 4 5 26 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 104 152 (accept_3_2 19
  104 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 104 152 2 9 52 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 104 152
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 104 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 104 152 8 2 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 104 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 104 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 152 2 7 52 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 152 (accept_3_2 13 104 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 152 4 3 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 104 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 152 2 5 52 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 152
  (Polychromatic418967fa.accept_25_9_4_2_1_8206 9 104 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 152 8 1 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 152 (accept_3_2 7 104 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  152 2 3 52 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 152 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 104 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 152 4 1 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 104 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 104 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 152 2 1 52 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 152 (accept_3_2 1 104 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 152))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 103 152
  (Eq.refl Bool.true) (allA_of_3_0 50 103 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 102 152 (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 102 152 2 25 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 102 152 (accept_3_2 49 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 152 2 24 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 102 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 152 2 23 51 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 152
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 152 2 22 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 152 (accept_3_2 43 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 152 2 21 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 102 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 152 2 20 51 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 152
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 152 2 19 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 152 (accept_3_2 37 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 152 2 18 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 152 (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 102 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 152 2 17 51 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 152
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 152 2 16 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 152 (accept_3_2 31 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 152 2 15 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 102 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 152 2 14 51 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 152
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 152 2 13 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 152 (accept_3_2 25 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 152 2 12 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 102 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 152 2 11 51 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 152
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 152 2 10 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 152 (accept_3_2 19 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 152 2 9 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 152 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 102 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 152 2 8 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  102 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 152 2 7 51 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 152 (accept_3_2 13
  102 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 152 2 6 51 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 152 2 5 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 102 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 102 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 152 2 4 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 152 (accept_3_2 7 102 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 102 152 2 3 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 102 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 102 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 152 2 2 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 152 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  102 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 152 2 1 51 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 152 (accept_3_2 1
  102 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 152)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 101 152 (Eq.refl Bool.true) (allA_succ_of_accept 51 101 152 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 152 (accept_3_2 49 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 152 (Polychromatic418967fa.accept_14_5_3_12_1_324 47 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 152 (accept_3_2 46 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 152 (accept_3_2 43 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 101 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 152 (accept_3_2 40 101 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 152
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 152 (accept_3_2 37 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 152 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 152 (accept_3_2 34 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 152 (accept_3_2 31 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 101 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 152 (accept_3_2 28 101 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 152
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 152 (accept_3_2 25 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 101 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 152 (accept_3_2 22 101 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 152
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 152 (accept_3_2 19 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 152 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 152 (Polychromatic418967fa.accept_23_17_9_14_1_8205 17 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 152 (accept_3_2 16 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 152 (accept_3_2 13 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 152 (Polychromatic418967fa.accept_16_11_5_8_1_2427 11 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 152 (accept_3_2 10 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 152 (accept_3_2 7 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 152 (accept_3_2 4 101 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 152 (accept_3_2 1 101 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  152)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 100 152 (Eq.refl Bool.true) (allA_of_3_0 53 100
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 99 152 (Eq.refl Bool.true) (allA_succ_of_accept 53 99 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 152 (accept_3_2 52 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  99 152 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 99 152 (Polychromatic418967fa.accept_13_11_8_9_1_1161 50 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 152 (accept_3_2 49 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 99 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 152 (accept_3_2 46 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  99 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 152 (Polychromatic418967fa.accept_16_12_3_8_1_5729 44 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 152 (accept_3_2 43 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 152 (accept_3_2 40 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 99 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 152 (accept_3_2 37 99 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 152 (Polychromatic418967fa.accept_16_4_3_8_1_2486 36 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 152 (accept_3_2 34 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 152 (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 99 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 152 (accept_3_2 31 99 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 152 (accept_3_2 28 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 152 (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 152 (accept_3_2 25 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 152 (accept_3_2 22 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 152 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 99 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 152 (accept_3_2 19 99 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 152 (accept_3_2 16 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 152 (Polychromatic418967fa.accept_17_15_14_16_1_5625 15 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 152 (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 99 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 152 (accept_3_2 13 99 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 152 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 152 (accept_3_2 10 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 152 (Polychromatic418967fa.accept_20_9_19_12_1_5221 9 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 152 (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 99 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 152 (accept_3_2 7 99 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 99 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 152 (accept_3_2 4 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  152 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 152 (Polychromatic418967fa.accept_17_2_14_16_1_2187 2 99 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 152 (accept_3_2 1 99 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 152)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 98 152 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 98 152 2 27 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 98 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 152 2 26 49 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 152
  (Polychromatic418967fa.accept_15_6_8_2_1_104 51 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 152 2 25 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 98 152 (accept_3_2 49 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 98
  152 2 24 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  98 152 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 98 152 2 23 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 98 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 98 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 98 152 2 22 49 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 98 152 (accept_3_2 43 98 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 152 2 21 49 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 152
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 98 152 2 20 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 98 152 (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 98 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 152 2 19 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 152 (accept_3_2 37 98 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 152 2 18 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 98 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 98 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 152 2 17 49 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 152
  (Polychromatic418967fa.accept_21_12_14_5_1_8204 33 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 152 2 16 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 98 152 (accept_3_2 31 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98
  152 2 15 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  98 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 98 152 2 14 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 98 152 (Polychromatic418967fa.accept_24_3_2_8_1_4572 27 98 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 152 2 13 49 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 152 (accept_3_2 25 98 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 152 2 12 49 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 152
  (Polychromatic418967fa.accept_11_1_10_9_1_871 23 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 98 152 2 11 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 98 152 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 98 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 152 2 10 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 152 (accept_3_2 19 98 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 152 2 9 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 98 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 152 2 8 49 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 152
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 152 2 7 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 152 (accept_3_2 13 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  152 2 6 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 152 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 152 2 5 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 152 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 98 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 152 2 4 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 152 (accept_3_2 7 98 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 152 2 3 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 98 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 152 2 2 49 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 152
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 152 2 1 49 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 152 (accept_3_2 1 98 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  152))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 97 152 (Eq.refl Bool.true) (allA_of_3_0 56
  97 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 96 152 (Eq.refl Bool.true) (allA_succ_of_gcd 56 96 152
  8 7 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96
  152 (accept_3_2 55 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 152 2 27 48 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 152
  (Polychromatic418967fa.accept_13_1_5_9_1_226 53 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 96 152 4 13 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 96 152 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 96 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 152 2 25 48 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 152 (accept_3_2 49 96 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 152 8 6 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 96 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 152 2 23 48 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 152
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 45 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 152 4 11 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 152 (accept_3_2 43 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96
  152 2 21 48 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  96 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 96 152 8 5 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 96 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 96 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 152 2 19 48 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 152 (accept_3_2 37 96 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 152 4 9 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 152 (Polychromatic418967fa.accept_21_14_12_5_1_8175 35 96
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 152 2 17 48 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 152
  (Polychromatic418967fa.accept_22_11_8_20_1_8203 33 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 152 8 4 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 152 (accept_3_2 31 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96
  152 2 15 48 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  96 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 96 152 4 7 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 152 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 96 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 152 2 13 48 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 152 (accept_3_2 25 96 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 152 8 3 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 152 2 11 48 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 152
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 152 4 5 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 152 (accept_3_2 19 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  152 2 9 48 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 152 (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 152 8 2 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 152 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 96 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 152 2 7 48 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 152 (accept_3_2 13 96 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 152 4 3 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 96 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 96 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 152 2 5 48 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 152
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 9 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 152 8 1 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 152 (accept_3_2 7 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 152
  2 3 48 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  152 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 152 4 1 24 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 152 2 1 48 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 152 (accept_3_2 1 96 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96 152))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 95 152 (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 95 152 19 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 95 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 152 (accept_3_2 55 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 152 (Polychromatic418967fa.accept_21_12_11_5_1_6549 54 95 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 152
  (Polychromatic418967fa.accept_10_3_5_2_1_38 53 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 152 (accept_3_2 52 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 152 (accept_3_2 49 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 95 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 152
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 152 (accept_3_2 46 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 152 (accept_3_2 43 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 152 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 95 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 152
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 152 (accept_3_2 40 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 95 152 19 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 95 152 (accept_3_2 37 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 95 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 95 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 152 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 95 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 152 (accept_3_2 34 95 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 152
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 32 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 152 (accept_3_2 31 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 152 (accept_3_2 28 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 152
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 152 (accept_3_2 25 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 152 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 152 (accept_3_2 22 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 152
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 19 95 152 19 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 18 95 152 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 95 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 152 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 95 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 152 (accept_3_2 16 95 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 152
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 152 (accept_3_2 13 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 152 (accept_3_2 10 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 152 (accept_3_2 7 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  152 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 152 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 95 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 152 (accept_3_2 4 95 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  95 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 152 (accept_3_2 1 95 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 94 152 (Eq.refl Bool.true) (allA_of_3_0 59 94 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  60 93 152 (Eq.refl Bool.true) (allA_succ_of_accept 59 93 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 152 (accept_3_2 58 93 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 152 (Polychromatic418967fa.accept_13_5_2_9_1_1195
  57 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 152 (accept_3_2 55 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 152 (accept_3_2 52 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 93 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 152 (accept_3_2 49 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 152 (Polychromatic418967fa.accept_17_14_8_16_1_6863 48 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 152 (accept_3_2 46 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 93 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 152
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 44 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 152 (accept_3_2 43 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 152 (accept_3_2 40 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 93 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 152
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 152 (accept_3_2 37 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 152 (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 152 (accept_3_2 34 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 93 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 152
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 152 (accept_3_2 31 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 152 (accept_3_2 28 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 152 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 93 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 152
  (Polychromatic418967fa.accept_17_9_8_16_1_2176 26 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 152 (accept_3_2 25 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 152 (accept_3_2 22 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 152 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 93 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 152 (accept_3_2 19 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 152 (accept_3_2 16 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 93 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 152 (accept_3_2 13 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 152 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 152 (accept_3_2 10 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 152 (Polychromatic418967fa.accept_17_9_8_16_1_2176 9 93 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 152
  (Polychromatic418967fa.accept_26_8_15_22_1_8202 8 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 152 (accept_3_2 7 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  152 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 152 (accept_3_2 4 93 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 93 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  93 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 152 (accept_3_2 1 93 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 92 152 (Eq.refl Bool.true) (allA_succ_of_gcd 60 92 152 4 15 23 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 152
  (Polychromatic418967fa.accept_7_3_1_5_1_44 59 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 92 152 2 29 46 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 92 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 92 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 92 152 4 14 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 92 152 (accept_3_2 55 92 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92 152 2 27 46 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 92 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 92 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 92 152 4 13 23 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 152
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 92 152 2 25 46 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 92 152 (accept_3_2 49 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92
  152 4 12 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  92 152 (Polychromatic418967fa.accept_13_8_1_9_1_1178 47 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 92 152 2 23 46 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 92 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 92 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 152 4 11 23 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 152 (accept_3_2 43 92 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 152 2 21 46 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 152
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 92 152 4 10 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 92 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 92 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 152 2 19 46 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 152 (accept_3_2 37 92 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 152 4 9 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 92 152 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 92 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 152 2 17 46 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 152
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 152 4 8 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 92 152 (accept_3_2 31 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92
  152 2 15 46 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  92 152 (Polychromatic418967fa.accept_16_13_12_8_1_2451 29 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 92 152 4 7 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 92 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 92 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 152 2 13 46 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 152 (accept_3_2 25 92 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 152 4 6 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 92 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 152 2 11 46 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 152
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 152 4 5 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 152 (accept_3_2 19 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  152 2 9 46 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 152 4 4 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 92 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 152 2 7 46 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 152 (accept_3_2 13 92 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 152 4 3 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 92 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 92 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 152 2 5 46 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 152
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 152 4 2 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 152 (accept_3_2 7 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 152
  2 3 46 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 92 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 152 4 1 23 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 92 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 152 2 1 46 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 152 (accept_3_2 1 92 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 91 152
  (Eq.refl Bool.true) (allA_of_3_0 62 91 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 90 152 (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 90 152 2 31 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 90 152 (accept_3_2 61 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 152 2 30 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 90 152 (Polychromatic418967fa.accept_11_4_2_9_1_496 59 90 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 152 2 29 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 57
  90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 152 2 28 45 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 152 (accept_3_2 55
  90 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 152 2 27 45 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 152
  (Polychromatic418967fa.accept_7_4_6_5_1_141 53 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 90 152 2 26 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 90 152 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 90 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 152 2 25 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 152 (accept_3_2 49 90 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 152 2 24 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 152 (Polychromatic418967fa.accept_13_8_12_9_1_1168 47 90 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 152 2 23 45 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 152
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 152 2 22 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 90 152 (accept_3_2 43 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90
  152 2 21 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  90 152 (Polychromatic418967fa.accept_14_13_6_12_1_3126 41 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 90 152 2 20 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 90 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 90 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 152 2 19 45 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 152 (accept_3_2 37 90 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 152 2 18 45 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 152
  (Polychromatic418967fa.accept_17_1_5_16_1_5589 35 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 90 152 2 17 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 90 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 90 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 152 2 16 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 152 (accept_3_2 31 90 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 152 2 15 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 90 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 152 2 14 45 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 152 2 13 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 90 152 (accept_3_2 25 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90
  152 2 12 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  90 152 (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 90 152 2 11 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 90 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 152 2 10 45 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 152 (accept_3_2 19 90 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 152 2 9 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 152 (Polychromatic418967fa.accept_25_17_15_2_1_8201
  17 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 152 2 8 45 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 152
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 90 152 2 7 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 90 152 (accept_3_2 13 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90
  152 2 6 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  90 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 152 2 5 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 90 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 152 2 4 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 152 (accept_3_2 7 90 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 152 2 3 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 90 152 (Polychromatic418967fa.accept_20_5_10_12_1_8200 5 90 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 152 2 2 45 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 152 2 1 45 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 152 (accept_3_2 1 90 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 89 152 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 89 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 89 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 89 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 152 (accept_3_2 61 89 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 152 (Polychromatic418967fa.accept_13_8_11_9_1_593
  60 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 152
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 59 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 152 (accept_3_2 58 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 152 (Polychromatic418967fa.accept_17_5_4_16_1_6925 56 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 152 (accept_3_2 55 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 152 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 89
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 152
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 53 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 152 (accept_3_2 52 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 89 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 152 (accept_3_2 49 89 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 152 (Polychromatic418967fa.accept_15_3_14_2_1_1888 48 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 152
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 152 (accept_3_2 46 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 152 (Polychromatic418967fa.accept_16_12_9_8_1_2508 44 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 152 (accept_3_2 43 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 152 (Polychromatic418967fa.accept_15_12_14_2_1_3794 42 89
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 152
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 152 (accept_3_2 40 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 89 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 152 (accept_3_2 37 89 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 152 (Polychromatic418967fa.accept_16_4_9_8_1_2509 36 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 152
  (Polychromatic418967fa.accept_14_7_5_12_1_1439 35 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 152 (accept_3_2 34 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 152 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 152 (accept_3_2 31 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 152 (Polychromatic418967fa.accept_22_8_1_20_1_6508 30 89
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 152
  (Polychromatic418967fa.accept_23_6_20_14_1_8199 29 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 152 (accept_3_2 28 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 152 (accept_3_2 25 89 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 152 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 152
  (Polychromatic418967fa.accept_16_7_9_8_1_829 23 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 152 (accept_3_2 22 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 152 (Polychromatic418967fa.accept_13_7_11_9_1_1858 20 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 152 (accept_3_2 19 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 152 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 89
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 152
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 152 (accept_3_2 16 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 89 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 152 (accept_3_2 13 89 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 152 (Polychromatic418967fa.accept_15_12_14_2_1_3794 12 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 152
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 152 (accept_3_2 10 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 152 (Polychromatic418967fa.accept_13_8_11_9_1_593 8 89 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 152 (accept_3_2 7 89 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 152 (Polychromatic418967fa.accept_23_6_20_14_1_8199 6 89 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 152
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 152 (accept_3_2 4 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 89 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 152 (accept_3_2 1 89 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 88 152
  (Eq.refl Bool.true) (allA_of_3_0 65 88 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 87 152 (Eq.refl
  Bool.true) (allA_succ_of_accept 65 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 152 (accept_3_2 64 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 152 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 87 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 152
  (Polychromatic418967fa.accept_20_2_7_12_1_5215 62 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 152 (accept_3_2 61 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 152 (Polychromatic418967fa.accept_16_12_7_8_1_1589 60 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 152 (accept_3_2 58 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 87 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 152 (accept_3_2 55 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 152 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 152 (accept_3_2 52 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 87 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 152 (accept_3_2 49 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 152 (accept_3_2 46 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 152 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 87 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 152 (accept_3_2 43 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 152 (accept_3_2 40 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 87 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 152 (accept_3_2 37 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 152 (accept_3_2 34 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 152 (Polychromatic418967fa.accept_14_5_3_12_1_324 33 87 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 152 (accept_3_2 31 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 152 (accept_3_2 28 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 152 (Polychromatic418967fa.accept_21_6_3_5_1_8198 27 87 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 152
  (Polychromatic418967fa.accept_20_6_7_12_1_8197 26 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 152 (accept_3_2 25 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 152 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 152 (accept_3_2 22 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 152 (accept_3_2 19 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 152 (accept_3_2 16 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 152 (accept_3_2 13 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 152 (accept_3_2 10 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 87 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 152 (accept_3_2 7 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  152 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 87 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 152 (accept_3_2 4 87 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 87
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 152 (accept_3_2 1 87 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 86 152 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 86 152 2 33 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 86 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 86 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 152 2 32 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 152 (Polychromatic418967fa.accept_13_11_8_9_1_1161
  63 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 86 152 2 31 43 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 86 152 (accept_3_2 61
  86 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 86 152 2 30 43 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 86 152
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 86 152 2 29 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 86 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 86 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 86 152 2 28 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 86 152 (accept_3_2 55 86 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86 152 2 27 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 86 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 86 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 152 2 26 43 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 152
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 152 2 25 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 86 152 (accept_3_2 49 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86
  152 2 24 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  86 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 86 152 2 23 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 86 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 86 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 152 2 22 43 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 152 (accept_3_2 43 86 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 152 2 21 43 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 152
  (Polychromatic418967fa.accept_10_1_6_2_1_867 41 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 86 152 2 20 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 86 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 86 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 152 2 19 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 152 (accept_3_2 37 86 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 152 2 18 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 152 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 86 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 152 2 17 43 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 152
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 152 2 16 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 86 152 (accept_3_2 31 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86
  152 2 15 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  86 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 86 152 2 14 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 86 152 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 86 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 152 2 13 43 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 152 (accept_3_2 25 86 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 152 2 12 43 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 152
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 152 2 11 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 86 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 152 2 10 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 152 (accept_3_2 19 86 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 152 2 9 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 86 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 152 2 8 43 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 152
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 152 2 7 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 152 (accept_3_2 13 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  152 2 6 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 152 2 5 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 152 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 86 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 152 2 4 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 152 (accept_3_2 7 86 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 152 2 3 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 86 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 152 2 2 43 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 152
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 152 2 1 43 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 152 (accept_3_2 1 86 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 85 152 (Eq.refl Bool.true)
  (allA_of_3_0 68 85 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 84 152 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 84 152 4 17 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 84 152 (accept_3_2 67 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84
  152 2 33 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  84 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 84 152 4 16 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 84 152 (Polychromatic418967fa.accept_16_15_4_8_1_1562 63 84 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 152 2 31 42 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 152 (accept_3_2 61 84 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 152 4 15 21 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 152 2 29 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 84 152 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 84 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 152 4 14 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 152 (accept_3_2 55 84 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 152 2 27 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 152 (Polychromatic418967fa.accept_13_1_6_9_1_1197 53 84 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 152 4 13 21 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 152
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 152 2 25 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 84 152 (accept_3_2 49 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84
  152 4 12 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  84 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 84 152 2 23 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 84 152 (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 84 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 152 4 11 21 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 152 (accept_3_2 43 84 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 152 2 21 42 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 152 4 10 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 84 152 (Polychromatic418967fa.accept_16_7_4_8_1_2487 39 84 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 152 2 19 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 152 (accept_3_2 37 84 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 152 4 9 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 84 152 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 84 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 152 2 17 42 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 152
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 152 4 8 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 152 (accept_3_2 31 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84
  152 2 15 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  84 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 84 152 4 7 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 84 152 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 84 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 152 2 13 42 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 152 (accept_3_2 25 84 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 152 4 6 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 152 2 11 42 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 152
  (Polychromatic418967fa.accept_16_5_4_8_1_1560 21 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 152 4 5 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 152 (accept_3_2 19 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  152 2 9 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 152 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 152 4 4 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 152 2 7 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 152 (accept_3_2 13 84 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 152 4 3 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 84 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 152 2 5 42 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 152
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 152 4 2 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 152 (accept_3_2 7 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 152
  2 3 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  152 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 152 4 1 21 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 152 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 84 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 152 2 1 42 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 152 (accept_3_2 1 84 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 83
  152 (Eq.refl Bool.true) (allA_succ_of_accept 69 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 83 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 83 152 (accept_3_2 67 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  83 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 83 152 (Polychromatic418967fa.accept_10_5_3_2_1_899 65 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 83 152 (accept_3_2 64 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 152
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 83 152 (accept_3_2 61 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  83 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 83 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 83 152 (accept_3_2 58 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 152
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 56 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 83 152 (accept_3_2 55 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  83 152 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 83 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 83 152 (accept_3_2 52 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 152
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 83 152 (accept_3_2 49 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  83 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 83 152 (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 152 (accept_3_2 46 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 152
  (Polychromatic418967fa.accept_16_12_3_8_1_5729 44 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 83 152 (accept_3_2 43 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  83 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 83 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 152 (accept_3_2 40 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 152
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 83 152 (accept_3_2 37 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  83 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 83 152 (Polychromatic418967fa.accept_10_5_3_2_1_899 35 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 152 (accept_3_2 34 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 152
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 152 (accept_3_2 31 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 152 (accept_3_2 28 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 152
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 152 (accept_3_2 25 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 152 (accept_3_2 22 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 152
  (Polychromatic418967fa.accept_14_6_13_12_1_810 20 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 152 (accept_3_2 19 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 152 (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 152 (accept_3_2 16 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 152 (accept_3_2 13 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 152 (accept_3_2 10 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 152
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 152 (accept_3_2 7 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  152 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 152 (accept_3_2 4 83 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  83 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 152 (accept_3_2 1 83 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 82 152 (Eq.refl Bool.true)
  (allA_of_3_0 71 82 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 81 152 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 152 (accept_3_2 70 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 81 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 152 (Polychromatic418967fa.accept_11_2_4_9_1_484
  68 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 152 (accept_3_2 67
  81 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 152
  (Polychromatic418967fa.accept_10_6_1_2_1_874 66 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 152 (accept_3_2 64 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 81 152 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 62
  81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 152 (accept_3_2 61 81
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 152
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 60 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 152 (accept_3_2 58 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 81 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 152 (Polychromatic418967fa.accept_10_6_1_2_1_874
  56 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 152 (accept_3_2 55
  81 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 152
  (Polychromatic418967fa.accept_12_6_9_8_1_165 54 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 152 (accept_3_2 52 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 81 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 50
  81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 152 (accept_3_2 49 81
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 152
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 152 (accept_3_2 46 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 81 152 (Polychromatic418967fa.accept_13_6_3_9_1_1827 45 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 44
  81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 152 (accept_3_2 43 81
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 152
  (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 152 (accept_3_2 40 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 81 152 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 152 (Polychromatic418967fa.accept_13_12_3_9_1_4341
  38 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 152 (accept_3_2 37
  81 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 152 (accept_3_2 34 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 81 152 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 152 (Polychromatic418967fa.accept_13_6_3_9_1_1827
  32 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 152 (accept_3_2 31
  81 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 152
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 152 (accept_3_2 28 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 81 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 152 (Polychromatic418967fa.accept_10_6_1_2_1_874
  26 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 152 (accept_3_2 25
  81 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 152
  (Polychromatic418967fa.accept_11_2_4_9_1_484 24 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 152 (accept_3_2 22 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 81 152 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 20
  81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 152 (accept_3_2 19 81
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 152
  (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 152 (accept_3_2 16 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 81 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 152
  (Polychromatic418967fa.accept_21_14_18_5_1_8196 14 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 152 (accept_3_2 13 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 152 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 152 (accept_3_2 10 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 152 (accept_3_2 7 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  152 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 152 (accept_3_2 4 81 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 152 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 81 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  81 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 152 (accept_3_2 1 81 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 80 152 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 80 152 8 9 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 80 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 80 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 152 2 35 40 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 152 (Polychromatic418967fa.accept_17_1_12_16_1_2211
  69 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 152 4 17 20 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 152 (accept_3_2 67
  80 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 152 2 33 40 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 80 152 8 8 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 80 152 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 80 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 152 2 31 40 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 152 (accept_3_2 61 80 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 152 4 15 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 152 (Polychromatic418967fa.accept_13_7_2_9_1_1826 59 80 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 152 2 29 40 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 152 8 7 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 152 (accept_3_2 55 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  152 2 27 40 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  80 152 (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 152 4 13 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 80 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 152 2 25 40 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 152 (accept_3_2 49 80 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 152 8 6 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 152 (Polychromatic418967fa.accept_14_5_10_12_1_1454
  47 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 152 2 23 40 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 152
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 152 4 11 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 152 (accept_3_2 43 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  152 2 21 40 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  80 152 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 152 8 5 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 80 152 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 80 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 152 2 19 40 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 152 (accept_3_2 37 80 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 152 4 9 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 152 (Polychromatic418967fa.accept_17_1_12_16_1_2211 35 80
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 152 2 17 40 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 152
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 33 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 152 8 4 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 152 (accept_3_2 31 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  152 2 15 40 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  80 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 152 4 7 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 152 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 80 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 152 2 13 40 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 152 (accept_3_2 25 80 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 152 8 3 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 80 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 152 2 11 40 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 152
  (Polychromatic418967fa.accept_25_21_5_2_1_8195 21 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 152 4 5 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 152 (accept_3_2 19 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  152 2 9 40 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 152 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 152 8 2 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 80 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 152 2 7 40 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 152 (accept_3_2 13 80 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 152 4 3 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 80 152 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 80 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 152 2 5 40 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 152 8 1 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 152 (accept_3_2 7 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 152
  2 3 40 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  152 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 80 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 80 152 4 1 20 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 152 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 80 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 152 2 1 40 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 152 (accept_3_2 1 80 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 74 79 152 (Eq.refl Bool.true) (allA_of_3_0 74 79 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  75 78 152 (Eq.refl Bool.true) (allA_succ_of_gcd 74 78 152 2 37 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 152 (accept_3_2 73 78 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 78 152 2 36 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 78 152 (Polychromatic418967fa.accept_21_8_15_5_1_8178 71 78 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 152 2 35 39 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 152
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 152 2 34 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 152 (accept_3_2 67 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78
  152 2 33 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  78 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 78 152 2 32 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 78 152 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 78 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 152 2 31 39 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 152 (accept_3_2 61 78 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 152 2 30 39 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 152
  (Polychromatic418967fa.accept_7_3_1_5_1_44 59 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 78 152 2 29 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 78 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 78 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 152 2 28 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 152 (accept_3_2 55 78 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 152 2 27 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 78 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 152 2 26 39 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 152 2 25 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 152 (accept_3_2 49 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78
  152 2 24 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  78 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 78 152 2 23 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 78 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 78 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 152 2 22 39 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 152 (accept_3_2 43 78 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 152 2 21 39 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 152
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 78 152 2 20 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 78 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 78 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 152 2 19 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 152 (accept_3_2 37 78 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 152 2 18 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 78 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 152 2 17 39 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 152
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 152 2 16 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 152 (accept_3_2 31 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78
  152 2 15 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  78 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 78 152 2 14 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 78 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 78 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 152 2 13 39 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 152 (accept_3_2 25 78 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 152 2 12 39 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 152 2 11 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 78 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 152 2 10 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 152 (accept_3_2 19 78 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 152 2 9 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 78 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 78 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 152 2 8 39 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 152
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 78 152 2 7 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 152 (accept_3_2 13 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78
  152 2 6 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  78 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 152 2 5 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 78 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 152 2 4 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 152 (accept_3_2 7 78 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 152 2 3 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 78 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 78 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 152 2 2 39 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 152
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 152 2 1 39 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 152 (accept_3_2 1 78 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 77 152 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 77 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 74
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 152 (accept_3_2 73 77
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 152
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 72 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 77 152 (Polychromatic418967fa.accept_18_17_5_8_1_1898 71 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 77 152 (accept_3_2 70 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 152 (Polychromatic418967fa.accept_13_3_12_9_1_1193
  68 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 152 (accept_3_2 67
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 152
  (Polychromatic418967fa.accept_9_3_5_8_1_99 66 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 77 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 77 152 (accept_3_2 64 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 77 152 (Polychromatic418967fa.accept_12_2_5_8_1_159
  62 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 152 (accept_3_2 61
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 152
  (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 77 152 (Polychromatic418967fa.accept_10_9_7_2_1_887 59 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 152 (accept_3_2 58 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 77 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 152 (accept_3_2 55 77
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 152
  (Polychromatic418967fa.accept_10_4_7_2_1_211 54 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 77 152 (Polychromatic418967fa.accept_16_5_13_8_1_2454 53 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 152 (accept_3_2 52 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 152 (Polychromatic418967fa.accept_12_2_5_8_1_159
  50 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 152 (accept_3_2 49
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 152
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 77 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 152 (accept_3_2 46 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 152 (Polychromatic418967fa.accept_10_4_7_2_1_211
  44 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 152 (accept_3_2 43
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 152
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 77 152 (Polychromatic418967fa.accept_21_20_14_5_1_8194 41 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 77 152 (accept_3_2 40 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 38
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 152 (accept_3_2 37 77
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 152
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 77 152 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 152 (accept_3_2 34 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 152 (Polychromatic418967fa.accept_18_14_5_8_1_1880
  32 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 152 (accept_3_2 31
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 152
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 77 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 152 (accept_3_2 28 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 152 (Polychromatic418967fa.accept_12_2_5_8_1_159
  26 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 152 (accept_3_2 25
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 152
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 77 152 (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 152 (accept_3_2 22 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 152 (accept_3_2 19 77
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 152
  (Polychromatic418967fa.accept_21_18_14_5_1_8193 18 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 77 152 (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 152 (accept_3_2 16 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 152 (Polychromatic418967fa.accept_10_4_7_2_1_211
  14 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 152 (accept_3_2 13
  77 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 152
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 77 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 152 (accept_3_2 10 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 77 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 152 (Polychromatic418967fa.accept_13_8_12_9_1_1168
  8 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 152 (accept_3_2 7 77
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 152 (Polychromatic418967fa.accept_9_6_5_8_1_598
  6 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 152
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 152 (accept_3_2 4 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 152 (accept_3_2 1 77 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 76
  152 (allA_of_3_0 76 76 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 152 (allA_succ_of_accept 74 75 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 152 (accept_3_2 73 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 152 (Polychromatic418967fa.accept_21_9_12_5_1_317 72 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 152 (accept_3_2 70 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 152 (accept_3_2 67 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 152 (accept_3_2 64 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 152 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 152
  (Polychromatic418967fa.accept_22_18_9_20_1_6474 62 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 152 (accept_3_2 61 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 152 (accept_3_2 58 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 152 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 152 (accept_3_2 55 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 152 (accept_3_2 52 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 152 (accept_3_2 49 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 152 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 152 (accept_3_2 46 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 152 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 152
  (Polychromatic418967fa.accept_16_12_11_8_1_832 44 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 152 (accept_3_2 43 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 152 (accept_3_2 40 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 152 (Polychromatic418967fa.accept_21_18_12_5_1_6592 39 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 152 (accept_3_2 37 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 152 (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 152 (accept_3_2 34 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 152 (accept_3_2 31 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 152 (accept_3_2 28 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 152 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 152
  (Polychromatic418967fa.accept_20_6_15_12_1_6637 26 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 152 (accept_3_2 25 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 152 (accept_3_2 22 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 152 (Polychromatic418967fa.accept_14_7_5_12_1_1439 21 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 152 (accept_3_2 19 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 152 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 152 (accept_3_2 16 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 152 (accept_3_2 13 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 152 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 152 (accept_3_2 10 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 152 (Polychromatic418967fa.accept_18_9_3_8_1_5419 9 75 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 152
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 152 (accept_3_2 7 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  152 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 152 (accept_3_2 4 75 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 152 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 75 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  75 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 152 (accept_3_2 1 75 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 152 (allA_succ_of_accept
  73 74 152 (accept_3_2 73 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 152 2 36 37 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 152 2 35 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 74 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 74 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 152 2 34 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 152 (accept_3_2 67 74 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 152 2 33 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 74 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 152 2 32 37 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 152
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 152 2 31 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 74 152 (accept_3_2 61 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74
  152 2 30 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  74 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 74 152 2 29 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 74 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 152 2 28 37 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 152 (accept_3_2 55 74 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 152 2 27 37 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 152
  (Polychromatic418967fa.accept_12_5_2_8_1_172 53 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 74 152 2 26 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 74 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 74 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 152 2 25 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 152 (accept_3_2 49 74 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 152 2 24 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 152 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 74 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 152 2 23 37 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 152
  (Polychromatic418967fa.accept_22_1_8_20_1_8192 45 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 152 2 22 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 74 152 (accept_3_2 43 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74
  152 2 21 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  74 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 74 152 2 20 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 74 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 74 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 152 2 19 37 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 152 (accept_3_2 37 74 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 152 2 18 37 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 152
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 74 152 2 17 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 74 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 74 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 152 2 16 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 152 (accept_3_2 31 74 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 152 2 15 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 74 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 152 2 14 37 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 152
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 152 2 13 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 74 152 (accept_3_2 25 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74
  152 2 12 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  74 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 74 152 2 11 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 74 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 74 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 152 2 10 37 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 152 (accept_3_2 19 74 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 152 2 9 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 152 (Polychromatic418967fa.accept_10_7_4_2_1_903 17
  74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 152 2 8 37 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 152 2 7 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 152 (accept_3_2 13 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  152 2 6 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 152 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 152 2 5 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 74 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 152 2 4 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 152 (accept_3_2 7 74 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 152 2 3 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 74 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 152 2 2 37 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 152
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 152 2 1 37 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 152 (accept_3_2 1 74 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 152 (allA_of_3_0 73 73 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 152 (allA_succ_of_accept 71 72 152
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 71 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 152 2 35 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 72 152 (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 72 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 152 4 17 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 152 (accept_3_2 67 72 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 152 2 33 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 152 (Polychromatic418967fa.accept_15_5_12_2_1_2820 65 72 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 152 8 8 9 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 152
  (Polychromatic418967fa.accept_13_11_7_9_1_612 63 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 152 2 31 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 152 (accept_3_2 61 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72
  152 4 15 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  72 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 72 152 2 29 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 72 152 (Polychromatic418967fa.accept_21_15_9_5_1_6588 57 72 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 152 8 7 9 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 152 (accept_3_2 55 72 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 152 2 27 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 53
  72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 152 4 13 18 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 152
  (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 152 2 25 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 72 152 (accept_3_2 49 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72
  152 8 6 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  72 152 (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 72 152 2 23 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 72 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 152 4 11 18 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 152 (accept_3_2 43 72 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 152 2 21 36 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 152
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 41 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 152 8 5 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 72 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 152 2 19 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 152 (accept_3_2 37 72 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 152 4 9 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 72 152 (Polychromatic418967fa.accept_14_7_2_12_1_1430 35 72 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 152 2 17 36 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 152
  (Polychromatic418967fa.accept_15_3_12_2_1_507 33 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 152 8 4 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 152 (accept_3_2 31 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  152 2 15 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  72 152 (Polychromatic418967fa.accept_13_3_7_9_1_1153 29 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 152 4 7 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 152 (Polychromatic418967fa.accept_28_27_16_12_1_8191 27 72 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 152 2 13 36 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 152 (accept_3_2 25 72 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 152 8 3 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 152 (Polychromatic418967fa.accept_25_23_22_2_1_8190
  23 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 152 2 11 36 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 152
  (Polychromatic418967fa.accept_13_8_7_9_1_611 21 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 152 4 5 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 152 (accept_3_2 19 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  152 2 9 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 152 8 2 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 152 (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 72 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 152 2 7 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 152 (accept_3_2 13 72 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 152 4 3 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 72 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 152 2 5 36 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 152
  (Polychromatic418967fa.accept_22_9_6_20_1_8174 9 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 152 8 1 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 152 (accept_3_2 7 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 152
  2 3 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  152 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 72 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 152 4 1 18 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 152 2 1 36 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 152 (accept_3_2 1 72 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 152 (allA_succ_of_accept 70 71 152 (accept_3_2 70 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 152 (Polychromatic418967fa.accept_13_3_6_9_1_1150 68 71 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 152 (accept_3_2 67 71 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 66
  71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 152
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 152 (accept_3_2 64 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 62 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 152 (accept_3_2 61 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 152
  (Polychromatic418967fa.accept_7_3_1_5_1_44 59 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 152 (accept_3_2 58 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 152 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 152 (accept_3_2 55 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 152 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 152
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 152 (accept_3_2 52 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 152 (accept_3_2 49 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 152
  (Polychromatic418967fa.accept_16_15_7_8_1_8189 47 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 152 (accept_3_2 46 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 152 (Polychromatic418967fa.accept_16_12_7_8_1_1589 44 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 152 (accept_3_2 43 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 152 (Polychromatic418967fa.accept_13_3_6_9_1_1150 42 71 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 152
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 152 (accept_3_2 40 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 152 (accept_3_2 37 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 152 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 152
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 152 (accept_3_2 34 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 152 (accept_3_2 31 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 152 (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 152
  (Polychromatic418967fa.accept_10_9_1_2_1_522 29 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 152 (accept_3_2 28 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 152 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 152 (accept_3_2 25 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 152
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 152 (accept_3_2 22 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 152 (accept_3_2 19 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 152
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 152 (accept_3_2 16 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 152 (accept_3_2 13 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 152 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 152
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 152 (accept_3_2 10 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 152 (Polychromatic418967fa.accept_25_8_21_2_1_8188 8 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 152 (accept_3_2 7 71 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 71 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 152
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 152 (accept_3_2 4 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 71 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 152 (accept_3_2 1 71 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 152
  (allA_of_3_0 70 70 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 152 (allA_succ_of_accept 68 69 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 152 (accept_3_2 67 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 152 (accept_3_2 64 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 152 (Polychromatic418967fa.accept_17_12_1_16_1_4360 63 69 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 152
  (Polychromatic418967fa.accept_14_6_13_12_1_810 62 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 152 (accept_3_2 61 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 152 (accept_3_2 58 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 69 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 152 (accept_3_2 55 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 152 (accept_3_2 52 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 152 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 69 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 152
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 152 (accept_3_2 49 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 152 (accept_3_2 46 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 152 (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 69 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 152
  (Polychromatic418967fa.accept_13_5_4_9_1_601 44 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 152 (accept_3_2 43 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 152 (accept_3_2 40 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 69 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 152 (accept_3_2 37 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 152 (accept_3_2 34 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 152 (Polychromatic418967fa.accept_13_7_4_9_1_1865 33 69 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 152
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 152 (accept_3_2 31 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 152 (accept_3_2 28 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 152 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 69 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 152
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 152 (accept_3_2 25 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 152 (Polychromatic418967fa.accept_21_3_6_5_1_8187 24 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 152 (accept_3_2 22 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 152 (accept_3_2 19 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 152 (accept_3_2 16 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 152 (accept_3_2 13 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 152 (accept_3_2 10 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 152 (Polychromatic418967fa.accept_22_9_3_20_1_8186 9 69 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 152
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 152 (accept_3_2 7 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  152 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 152 (accept_3_2 4 69 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  69 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 152 (accept_3_2 1 69 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 152 (allA_succ_of_accept 67 68
  152 (accept_3_2 67 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 152 2 33 34 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 152
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 152 4 16 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 152 (Polychromatic418967fa.accept_16_15_4_8_1_1562 63 68 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 152 2 31 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 152 (accept_3_2 61 68 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 152 4 15 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 152 (Polychromatic418967fa.accept_11_4_2_9_1_496 59 68 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 152 2 29 34 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 152
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 152 4 14 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 152 (accept_3_2 55 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  152 2 27 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  68 152 (Polychromatic418967fa.accept_16_5_4_8_1_1560 53 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 152 4 13 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 152 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 68 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 152 2 25 34 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 152 (accept_3_2 49 68 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 152 4 12 17 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 152
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 152 2 23 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 68 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 152 4 11 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 152 (accept_3_2 43 68 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 152 2 21 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 152 (Polychromatic418967fa.accept_13_2_3_9_1_2610 41 68 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 152 4 10 17 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 152
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 152 2 19 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 152 (accept_3_2 37 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  152 4 9 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 152 2 17 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 152 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 68 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 152 4 8 17 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 152 (accept_3_2 31 68 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 152 2 15 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 29
  68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 152 4 7 17 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 152
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 152 2 13 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 68 152 (accept_3_2 25 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68
  152 4 6 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  68 152 (Polychromatic418967fa.accept_16_7_4_8_1_2487 23 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 68 152 2 11 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 68 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 68 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 152 4 5 17 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 152 (accept_3_2 19 68 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 152 2 9 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68 152 (Polychromatic418967fa.accept_16_1_4_8_1_3434 17 68 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 152 4 4 17 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 152
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 152 2 7 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 152 (accept_3_2 13 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  152 4 3 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 152 2 5 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 152 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 68 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 152 4 2 17 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 152 (accept_3_2 7 68 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 152 2 3 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 152 4 1 17 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 152
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 152 2 1 34 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 152 (accept_3_2 1 68 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 152 (allA_of_3_0 67 67 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 152 (allA_succ_of_accept 65 66 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 152 2 32 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 152 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 66 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 152 2 31 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 152 (accept_3_2 61 66 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 152 2 30 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 66 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 152 2 29 33 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 152 2 28 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 152 (accept_3_2 55 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66
  152 2 27 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  66 152 (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 66 152 2 26 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 66 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 66 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 152 2 25 33 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 152 (accept_3_2 49 66 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 152 2 24 33 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 152 2 23 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 66 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 152 2 22 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 152 (accept_3_2 43 66 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 152 2 21 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 66 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 152 2 20 33 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 152 2 19 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 152 (accept_3_2 37 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66
  152 2 18 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  66 152 (Polychromatic418967fa.accept_17_1_15_16_1_2202 35 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 66 152 2 17 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 66 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 66 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 152 2 16 33 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 152 (accept_3_2 31 66 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 152 2 15 33 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 152 2 14 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 66 152 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 66 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 152 2 13 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 152 (accept_3_2 25 66 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 152 2 12 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 66 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 152 2 11 33 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 152
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 152 2 10 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 152 (accept_3_2 19 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66
  152 2 9 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  66 152 (Polychromatic418967fa.accept_20_17_6_12_1_8185 17 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 152 2 8 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 66 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 152 2 7 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 152 (accept_3_2 13 66 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 152 2 6 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 66 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 66 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 152 2 5 33 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 152 2 4 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 152 (accept_3_2 7 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 152
  2 3 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66
  152 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 66 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 152 2 2 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 66 152 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 66 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 152 2 1 33 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 152 (accept_3_2 1 66 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 152
  (allA_succ_of_accept 64 65 152 (accept_3_2 64 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 152 (accept_3_2 61 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 65 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 152
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 152 (accept_3_2 58 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 152 (Polychromatic418967fa.accept_11_1_10_9_1_871 56 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 152 (accept_3_2 55 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 152 (Polychromatic418967fa.accept_22_10_21_20_1_6534 54 65 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 152
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 152 (accept_3_2 52 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 152 (accept_3_2 49 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 65 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 152
  (Polychromatic418967fa.accept_10_7_5_2_1_880 47 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 152 (accept_3_2 46 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 152 (Polychromatic418967fa.accept_15_14_5_2_1_4761 44 65 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 152 (accept_3_2 43 65 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 152 (accept_3_2 40 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 152 (accept_3_2 37 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 152 (Polychromatic418967fa.accept_16_4_1_8_1_835 36 65 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 152
  (Polychromatic418967fa.accept_14_7_9_12_1_3975 35 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 152 (accept_3_2 34 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 152 (accept_3_2 31 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 65 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 152
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 152 (accept_3_2 28 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 152 (accept_3_2 25 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 152 (accept_3_2 22 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 152 (Polychromatic418967fa.accept_16_4_1_8_1_835 20 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 152 (accept_3_2 19 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 65 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 152
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 152 (accept_3_2 16 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 152 (accept_3_2 13 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 152
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 152 (accept_3_2 10 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 152 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 152 (accept_3_2 7 65 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 65 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 152 (accept_3_2 4 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 65 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 152 (accept_3_2 1 65 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 152
  (allA_of_3_0 64 64 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 152 (allA_succ_of_accept 62 63 152
  (Polychromatic418967fa.accept_17_11_12_16_1_3219 62 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 63 152 (accept_3_2 61 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 152 (Polychromatic418967fa.accept_13_8_11_9_1_593 60 63 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 152 (accept_3_2 58 63 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 152 (Polychromatic418967fa.accept_15_12_3_2_1_2756
  57 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 152
  (Polychromatic418967fa.accept_22_12_19_20_1_8184 56 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 63 152 (accept_3_2 55 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 152 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 63 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 152 (accept_3_2 52 63 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 152 (Polychromatic418967fa.accept_10_1_3_2_1_220
  51 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 152
  (Polychromatic418967fa.accept_15_5_3_2_1_5930 50 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 152 (accept_3_2 49 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 152 (Polychromatic418967fa.accept_25_23_13_2_1_8183 48 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 152 (accept_3_2 46 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 152 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 63 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 152
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 44 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 152 (accept_3_2 43 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 152 (accept_3_2 40 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 152 (Polychromatic418967fa.accept_16_7_15_8_1_278 39 63 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 152
  (Polychromatic418967fa.accept_29_9_5_7_1_8182 38 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 152 (accept_3_2 37 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 152 (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 152 (accept_3_2 34 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 152 (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 63 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 152
  (Polychromatic418967fa.accept_11_10_8_9_1_492 32 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 152 (accept_3_2 31 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 152 (accept_3_2 28 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 152 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 63 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 152
  (Polychromatic418967fa.accept_23_3_17_14_1_8181 26 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 152 (accept_3_2 25 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 152 (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 152 (accept_3_2 22 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 152 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 63 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 152
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 20 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 152 (accept_3_2 19 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 152 (accept_3_2 16 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 152 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 63 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 152
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 152 (accept_3_2 13 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 152 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 152 (accept_3_2 10 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 152 (Polychromatic418967fa.accept_14_9_7_12_1_4034 9 63 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 152
  (Polychromatic418967fa.accept_13_8_11_9_1_593 8 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 152 (accept_3_2 7 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  152 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 152 (accept_3_2 4 63 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 152 (Polychromatic418967fa.accept_18_3_9_8_1_2977 3 63 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 152 (Polychromatic418967fa.accept_13_2_11_9_1_591 2
  63 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 152 (accept_3_2 1 63 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 152 (allA_succ_of_accept 61 62 152
  (accept_3_2 61 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 152 2 30 31 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 152
  (Polychromatic418967fa.accept_12_11_2_8_1_511 59 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 152 2 29 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 62 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 152 2 28 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 152 (accept_3_2 55 62 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 152 2 27 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 62 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 152 2 26 31 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 152
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 51 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 152 2 25 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 152 (accept_3_2 49 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  152 2 24 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 152 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 152 2 23 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 152 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 62 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 152 2 22 31 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 152 (accept_3_2 43 62 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 152 2 21 31 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 152
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 152 2 20 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 62 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 152 2 19 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 152 (accept_3_2 37 62 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 152 2 18 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 152 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 62 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 152 2 17 31 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 152
  (Polychromatic418967fa.accept_24_9_14_8_1_6401 33 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 152 2 16 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 152 (accept_3_2 31 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  152 2 15 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 152 2 14 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 152 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 62 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 152 2 13 31 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 152 (accept_3_2 25 62 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 152 2 12 31 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 152
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 152 2 11 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 152 (Polychromatic418967fa.accept_23_21_16_14_1_8180 21 62 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 152 2 10 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 152 (accept_3_2 19 62 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 152 2 9 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 62 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 152 2 8 31 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 152
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 152 2 7 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 152 (accept_3_2 13 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  152 2 6 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 152 2 5 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 152 (Polychromatic418967fa.accept_20_9_2_12_1_5144 9 62 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 152 2 4 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 152 (accept_3_2 7 62 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 152 2 3 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 152 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 62 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 152 2 2 31 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 152
  (Polychromatic418967fa.accept_29_3_4_7_1_8179 3 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 152 2 1 31 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 152 (accept_3_2 1 62 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 152 (allA_of_3_0 61 61 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 152 (allA_succ_of_accept 59 60 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 152 2 29 30 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 152 4 14 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 152 (accept_3_2 55 60 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 152 2 27 30 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 152 (Polychromatic418967fa.accept_13_1_8_9_1_1154 53 60 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 152 4 13 15 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 152
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 152 2 25 30 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 152 (accept_3_2 49 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  152 4 12 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 152 2 23 30 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 60 152 (Polychromatic418967fa.accept_16_13_12_8_1_2451 45 60 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 152 4 11 15 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 152 (accept_3_2 43 60 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 152 2 21 30 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 152
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 152 4 10 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 152 2 19 30 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 152 (accept_3_2 37 60 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 152 4 9 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 60 152 (Polychromatic418967fa.accept_16_3_12_8_1_808 35 60 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 152 2 17 30 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 152
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 152 4 8 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 152 (accept_3_2 31 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  152 2 15 30 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 152 4 7 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 152 2 13 30 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 152 (accept_3_2 25 60 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 152 4 6 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 152 2 11 30 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 152
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 152 4 5 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 152 (accept_3_2 19 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  152 2 9 30 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 152 (Polychromatic418967fa.accept_13_4_8_9_1_1156 17 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 152 4 4 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 152 2 7 30 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 152 (accept_3_2 13 60 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 152 4 3 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 60 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 152 2 5 30 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 152
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 152 4 2 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 152 (accept_3_2 7 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 152
  2 3 30 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  152 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 60 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 152 4 1 15 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 152 2 1 30 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 152 (accept_3_2 1 60 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 152)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 152
  (allA_succ_of_accept 58 59 152 (accept_3_2 58 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 152 (accept_3_2 55 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 152 (Polychromatic418967fa.accept_13_2_7_9_1_2616 54 59 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 152
  (Polychromatic418967fa.accept_16_5_11_8_1_3431 53 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 152 (accept_3_2 52 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 152 (accept_3_2 49 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 152
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 152 (accept_3_2 46 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 152 (accept_3_2 43 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 152 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 152
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 152 (accept_3_2 40 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 152 (accept_3_2 37 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 59 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 152
  (Polychromatic418967fa.accept_11_2_4_9_1_484 35 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 152 (accept_3_2 34 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 152 (Polychromatic418967fa.accept_13_6_7_9_1_1848 32 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 152 (accept_3_2 31 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 59 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 152 (accept_3_2 28 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 152 (accept_3_2 25 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 152 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 152 (accept_3_2 22 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 152 (accept_3_2 19 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 152 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 59 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 152
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 152 (accept_3_2 16 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 152 (accept_3_2 13 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 152
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 152 (accept_3_2 10 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 152 (accept_3_2 7 59 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 152 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 59 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 152
  (Polychromatic418967fa.accept_14_5_3_12_1_324 5 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 152 (accept_3_2 4 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 59 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 152 (accept_3_2 1 59 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 152 (allA_of_3_0
  58 58 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 152 (allA_succ_of_accept 56 57 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 152 (accept_3_2 55 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 152 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 152 (accept_3_2 52 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 57 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 152 (accept_3_2 49 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 152 (accept_3_2 46 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 152
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 152 (accept_3_2 43 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 152 (accept_3_2 40 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 57 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 57 152 19 2 3 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 57 152 (accept_3_2 37 57 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 152 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 57
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 152 (accept_3_2 34 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  57 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 57 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 152 (accept_3_2 31 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 57 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 152 (accept_3_2 28 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  57 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 57 152 (Polychromatic418967fa.accept_11_4_2_9_1_496 26 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 152 (accept_3_2 25 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 152 (accept_3_2 22 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  57 152 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 57 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 57 152 19 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18 57 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 18
  57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 152 (accept_3_2 16 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  57 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 57 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 152 (accept_3_2 13 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 152 (Polychromatic418967fa.accept_16_12_9_8_1_2508 12 57 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 152 (accept_3_2 10 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  57 152 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 57 152 (Polychromatic418967fa.accept_21_8_15_5_1_8178 8 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 152 (accept_3_2 7 57 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 152 (accept_3_2 4 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57
  152 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 57 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 152 (accept_3_2 1 57 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 57 152))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 152
  (allA_succ_of_accept 55 56 152 (accept_3_2 55 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 56
  152 2 27 28 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  56 152 (Polychromatic418967fa.accept_17_2_5_16_1_1264 53 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 56 152 4 13 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 56 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 56 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 152 2 25 28 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 152 (accept_3_2 49 56 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 152 8 6 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 152 (Polychromatic418967fa.accept_13_8_4_9_1_1145
  47 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 152 2 23 28 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 152
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 56 152 4 11 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 56 152 (accept_3_2 43 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  152 2 21 28 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 56 152 8 5 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 56 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 56 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 152 2 19 28 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 152 (accept_3_2 37 56 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 152 4 9 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 56 152 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 56 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 152 2 17 28 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 152
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 152 8 4 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 152 (accept_3_2 31 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  152 2 15 28 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  56 152 (Polychromatic418967fa.accept_21_8_14_5_1_8177 29 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 152 4 7 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 152 (Polychromatic418967fa.accept_23_4_10_14_1_8176 27 56 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 152 2 13 28 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 152 (accept_3_2 25 56 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 152 8 3 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 152 2 11 28 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 152
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 152 4 5 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 152 (accept_3_2 19 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  152 2 9 28 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 152 (Polychromatic418967fa.accept_18_17_2_8_1_6800 17 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 152 8 2 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 56 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 152 2 7 28 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 152 (accept_3_2 13 56 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 152 4 3 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 152 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 152 2 5 28 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 152
  (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 152 8 1 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 152 (accept_3_2 7 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 152
  2 3 28 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 152 4 1 14 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 56 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 152 2 1 28 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 152 (accept_3_2 1 56 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 152)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 152 (allA_of_3_0 55
  55 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 152 (allA_succ_of_accept 53 54 152
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 152 2 26 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 152 (Polychromatic418967fa.accept_12_3_6_8_1_969 51 54 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 152 2 25 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 152 (accept_3_2 49 54 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 152 2 24 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 152 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 54 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 152 2 23 27 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 152
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 152 2 22 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 152 (accept_3_2 43 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  152 2 21 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 152 (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 152 2 20 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 152 (Polychromatic418967fa.accept_12_3_6_8_1_969 39 54 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 152 2 19 27 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 152 (accept_3_2 37 54 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 152 2 18 27 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 152
  (Polychromatic418967fa.accept_21_14_12_5_1_8175 35 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 152 2 17 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 152 2 16 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 152 (accept_3_2 31 54 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 152 2 15 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 152 (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 54 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 152 2 14 27 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 152
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 152 2 13 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 152 (accept_3_2 25 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54
  152 2 12 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  54 152 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 152 2 11 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 54 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 152 2 10 27 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 152 (accept_3_2 19 54 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 152 2 9 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 152 (Polychromatic418967fa.accept_10_7_4_2_1_903 17
  54 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 152 2 8 27 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 152 2 7 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 152 (accept_3_2 13 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  152 2 6 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 152 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 152 2 5 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 54 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 152 2 4 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 152 (accept_3_2 7 54 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 152 2 3 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 152 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 54 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 152 2 2 27 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 152 2 1 27 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 152 (accept_3_2 1 54 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  152)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 152 (allA_succ_of_accept 52 53 152 (accept_3_2
  52 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 152
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 53 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 152 (accept_3_2 49 53 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 152 (Polychromatic418967fa.accept_13_8_1_9_1_1178
  47 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 152 (accept_3_2 46
  53 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 152
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 53 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 152 (accept_3_2 43 53 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 152 (Polychromatic418967fa.accept_17_8_2_16_1_5598 42 53 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 152
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 152 (accept_3_2 40 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 152 (accept_3_2 37 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 152
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 152 (accept_3_2 34 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 152 (Polychromatic418967fa.accept_13_6_1_9_1_619 32 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 152 (accept_3_2 31 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 53 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 152 (accept_3_2 28 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 152 (accept_3_2 25 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 152 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 53 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 152
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 152 (accept_3_2 22 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 152 (accept_3_2 19 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 152 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 53 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 152
  (Polychromatic418967fa.accept_21_17_11_5_1_5060 17 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 152 (accept_3_2 16 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 152 (accept_3_2 13 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 152 (Polychromatic418967fa.accept_16_12_5_8_1_2492 12 53 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 152
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 152 (accept_3_2 10 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 152 (accept_3_2 7 53 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 53 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 152
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 152 (accept_3_2 4 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 53 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 152 (accept_3_2 1 53 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 152))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 152 (allA_of_3_0 52 52
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 152 (allA_succ_of_accept 50 51 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 152 (accept_3_2 49 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 152 (accept_3_2 46 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 51 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 152
  (Polychromatic418967fa.accept_16_12_3_8_1_5729 44 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 152 (accept_3_2 43 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 152 (accept_3_2 40 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 152
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 152 (accept_3_2 37 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 152 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 152 (accept_3_2 34 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 152 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 51 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 152
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 152 (accept_3_2 31 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 152 (accept_3_2 28 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 152 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 51 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 152
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 152 (accept_3_2 25 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 152 (accept_3_2 22 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 152 (accept_3_2 19 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 152 (accept_3_2 16 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 152 (Polychromatic418967fa.accept_21_15_9_5_1_6588 15 51 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 152 (accept_3_2 13 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 152 (accept_3_2 10 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 152 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 51 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 152
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 8 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 152 (accept_3_2 7 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  152 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 152 (accept_3_2 4 51 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  51 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 152 (accept_3_2 1 51 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 152)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 152 (allA_succ_of_accept 49 50 152 (accept_3_2 49 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 152 2 24 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 50 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 50 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 152 2 23 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 45
  50 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 152 2 22 25 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 152 (accept_3_2 43
  50 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 152 2 21 25 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 152
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 152 2 20 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 50 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 152 2 19 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 152 (accept_3_2 37 50 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 152 2 18 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 152 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 50 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 152 2 17 25 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 152
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 152 2 16 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 152 (accept_3_2 31 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  152 2 15 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 152 2 14 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 50 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 152 2 13 25 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 152 (accept_3_2 25 50 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 152 2 12 25 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 152
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 152 2 11 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 50 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 152 2 10 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 152 (accept_3_2 19 50 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 152 2 9 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 50 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 152 2 8 25 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 152
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 152 2 7 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 152 (accept_3_2 13 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  152 2 6 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 152 2 5 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 152 (Polychromatic418967fa.accept_22_9_6_20_1_8174 9 50 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 152 2 4 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 152 (accept_3_2 7 50 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 152 2 3 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 50 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 152 2 2 25 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 152
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 152 2 1 25 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 152 (accept_3_2 1 50 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  152)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 152 (allA_of_3_0 49 49 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 152 (allA_succ_of_accept 47 48 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 47
  48 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 152 2 23 24 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 152
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 152 4 11 12 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 152 (accept_3_2 43 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48
  152 2 21 24 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  48 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 152 8 5 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 48 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 152 2 19 24 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 152 (accept_3_2 37 48 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 152 4 9 12 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 48 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 152 2 17 24 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 152
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 152 8 4 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 152 (accept_3_2 31 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  152 2 15 24 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  48 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 152 4 7 12 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 152 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 48 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 152 2 13 24 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 152 (accept_3_2 25 48 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 152 8 3 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 23
  48 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 152 2 11 24 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 152
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 21 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 152 4 5 12 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 152 (accept_3_2 19 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  152 2 9 24 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 152 (Polychromatic418967fa.accept_22_17_4_20_1_8173 17 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 152 8 2 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 152 2 7 24 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 152 (accept_3_2 13 48 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 152 4 3 12 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 48 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 152 2 5 24 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 152
  (Polychromatic418967fa.accept_22_9_4_20_1_8172 9 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 152 8 1 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 152 (accept_3_2 7 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 152
  2 3 24 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  152 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 152 4 1 12 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 152 (Polychromatic418967fa.accept_18_3_12_8_1_5415 3 48 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 152 2 1 24 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 152 (accept_3_2 1 48 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 152)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 152 (allA_succ_of_accept 46
  47 152 (accept_3_2 46 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 152
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 152 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 47 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 152 (accept_3_2 43 47 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 41
  47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 152 (accept_3_2 40 47
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 152 (Polychromatic418967fa.accept_6_3_5_2_1_12
  39 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 152
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 152 (accept_3_2 37 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 152 (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 152 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 47 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 152 (accept_3_2 34 47 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 152 (accept_3_2 31 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 152 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 47 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 152 (accept_3_2 28 47 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 152
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 152 (accept_3_2 25 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 152 (accept_3_2 22 47 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 152
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 20 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 152 (accept_3_2 19 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 152 (Polychromatic418967fa.accept_24_18_23_8_1_8171 18 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 152 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 47 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 152 (accept_3_2 16 47 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 152 (accept_3_2 13 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 152 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 47 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 152 (accept_3_2 10 47 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 152
  (Polychromatic418967fa.accept_22_8_3_20_1_8170 8 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 152 (accept_3_2 7 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  152 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 152 (accept_3_2 4 47 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 152 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  47 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 152 (accept_3_2 1 47 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 152))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  152 (allA_of_3_0 46 46 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 152 (allA_succ_of_accept 44 45 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 152 (accept_3_2 43 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 152 (accept_3_2 40 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 152 (Polychromatic418967fa.accept_17_5_11_16_1_3257 39 45 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 152
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 152 (accept_3_2 37 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 152 (accept_3_2 34 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 152 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 45 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 152
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 152 (accept_3_2 31 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 152 (accept_3_2 28 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 152 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 45 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 152
  (Polychromatic418967fa.accept_20_6_5_12_1_8169 26 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 152 (accept_3_2 25 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 152 (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 152 (accept_3_2 22 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 152 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 45 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 152
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 20 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 152 (accept_3_2 19 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 152 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 152 (accept_3_2 16 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 45 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 152
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 152 (accept_3_2 13 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 152 (Polychromatic418967fa.accept_16_12_13_8_1_2409 12 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 152 (accept_3_2 10 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 152 (accept_3_2 7 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  152 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 45 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 152 (accept_3_2 4 45 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 152 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 45 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 45
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 152 (accept_3_2 1 45 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 152))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  152 (allA_succ_of_accept 43 44 152 (accept_3_2 43 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 152 2 21 22 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 44 152 (Polychromatic418967fa.accept_13_2_5_9_1_610 41 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 152 4 10 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 44 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 152 2 19 22 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 152 (accept_3_2 37 44 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 152 4 9 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 152 (Polychromatic418967fa.accept_14_7_2_12_1_1430
  35 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 152 2 17 22 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 152
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 33 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 152 4 8 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 152 (accept_3_2 31 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  152 2 15 22 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 152 (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 152 4 7 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 152 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 44 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 152 2 13 22 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 152 (accept_3_2 25 44 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 152 4 6 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 152 (Polychromatic418967fa.accept_16_7_12_8_1_2450 23 44 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 152 2 11 22 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 152
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 21 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 152 4 5 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 152 (accept_3_2 19 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  152 2 9 22 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 152 4 4 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 152 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 44 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 152 2 7 22 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 152 (accept_3_2 13 44 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 152 4 3 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 44 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 152 2 5 22 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 152
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 152 4 2 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 152 (accept_3_2 7 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 152
  2 3 22 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  152 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 44 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 44 152 4 1 11 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 44 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 44 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 152 2 1 22 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 152 (accept_3_2 1 44 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 44 152)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 152 (allA_of_3_0 43 43
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 152 (allA_succ_of_accept 41 42 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 152 2 20 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 152 2 19 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 152 (accept_3_2 37 42 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 152 2 18 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 152 (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 42 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 152 2 17 21 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 152
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 152 2 16 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 152 (accept_3_2 31 42 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42
  152 2 15 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  42 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 42 152 2 14 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 42 152 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 42 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 152 2 13 21 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 152 (accept_3_2 25 42 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 152 2 12 21 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 152
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 152 2 11 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 42 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 152 2 10 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 152 (accept_3_2 19 42 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 152 2 9 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 42 152 (Polychromatic418967fa.accept_20_17_2_12_1_8168 17 42 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 152 2 8 21 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 42 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 42 152 2 7 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 152 (accept_3_2 13 42 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42
  152 2 6 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  42 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 42 152 2 5 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 42 152 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 152 2 4 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 152 (accept_3_2 7 42 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 152 2 3 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 42 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 152 2 2 21 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 152
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 42 152 2 1 21 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 152 (accept_3_2 1 42 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  152)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 152 (allA_succ_of_accept 40 41 152 (accept_3_2 40 41 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 152
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 152 (accept_3_2 37 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 152 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 41 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 152 (accept_3_2 34 41 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 152
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 152 (accept_3_2 31 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 152 (accept_3_2 28 41 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 152
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 152 (accept_3_2 25 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 152 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 152 (Polychromatic418967fa.accept_10_3_1_2_1_521 23 41 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 152 (accept_3_2 22 41 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 152
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 152 (accept_3_2 19 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 152 (Polychromatic418967fa.accept_16_1_9_8_1_2438 17 41 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 152 (accept_3_2 16 41 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 152
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 152 (accept_3_2 13 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 41 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 152 (accept_3_2 10 41 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 152
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 152 (accept_3_2 7 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  152 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 152 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 41 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 152 (accept_3_2 4 41 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 41
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 152 (accept_3_2 1 41 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 152))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 152
  (allA_of_3_0 40 40 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 152 (allA_succ_of_accept 38 39 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 152 (accept_3_2 37 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 152 (accept_3_2 34 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 39 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 152 (accept_3_2 31 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 152 (accept_3_2 28 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 152
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 152 (accept_3_2 25 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 152 (accept_3_2 22 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 152 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 39 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 152
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 152 (accept_3_2 19 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 152 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 152 (accept_3_2 16 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 152 (accept_3_2 13 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 152 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 152 (accept_3_2 10 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 39 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 152 (accept_3_2 7 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  152 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 152 (accept_3_2 4 39 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 152 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 39 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  39 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 152 (accept_3_2 1 39 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 152))))))))))))))))))))))))))))))))))))))) (allB_succ 38 152
  (allA_succ_of_accept 37 38 152 (accept_3_2 37 38 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  152 2 18 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 38 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 152 2 17 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 152 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 38 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 152 2 16 19 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 152 (accept_3_2 31 38 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 152 2 15 19 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 38 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 152 2 14 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 152 (Polychromatic418967fa.accept_22_5_16_20_1_8167 27 38 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 152 2 13 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 152 (accept_3_2 25 38 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 152 2 12 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 38 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 152 2 11 19 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 152
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 38 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 152 2 10 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 19 38 152 19 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 38 152 2 9 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 38 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 152 2 8 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 38 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 152 2 7 19 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 152 (accept_3_2 13 38 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 152 2 6 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 152 (Polychromatic418967fa.accept_12_11_2_8_1_511
  11 38 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 152 2 5 19 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 38 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 152 2 4 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 152 (accept_3_2 7 38 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 152
  2 3 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 38 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 152 2 2 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 38 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 152 2 1 19 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 152 (accept_3_2 1 38 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 152)))))))))))))))))))))))))))))))))))))) (allB_succ 37 152 (allA_of_3_0 37 37 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 152 (allA_succ_of_accept 35 36 152
  (Polychromatic418967fa.accept_16_3_4_8_1_3450 35 36 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 152 2 17 18 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 152 (Polychromatic418967fa.accept_16_1_4_8_1_3434 33 36 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 152 4 8 9 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 152 (accept_3_2 31 36 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 36 152 2 15 18 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 36 152 (Polychromatic418967fa.accept_16_13_4_8_1_4557 29 36 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 152 4 7 9 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 152
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 152 2 13 18 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 152 (accept_3_2 25 36 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  152 4 6 9 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 152 (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 36 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 152 2 11 18 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 152 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 36 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 152 4 5 9 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 152 (accept_3_2 19 36 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 152 2 9 18 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 152 4 4 9 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 152
  (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 36 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 152 2 7 18 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 152 (accept_3_2 13 36 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  152 4 3 9 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 152 2 5 18 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 152 (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 36 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 152 4 2 9 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 152 (accept_3_2 7 36 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 152 2 3 18 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 152 (Polychromatic418967fa.accept_16_5_4_8_1_1560 5 36 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 152 4 1 9 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 152
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 152 2 1 18 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 152 (accept_3_2 1 36 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  152)))))))))))))))))))))))))))))))))))) (allB_succ 35 152 (allA_succ_of_accept 34 35 152 (accept_3_2 34 35 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 152
  (Polychromatic418967fa.accept_17_15_1_16_1_8166 32 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 152 (accept_3_2 31 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 152 (Polychromatic418967fa.accept_14_2_7_12_1_1485 30 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 152 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 35 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 152 (accept_3_2 28 35 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 152
  (Polychromatic418967fa.accept_11_4_2_9_1_496 26 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 152 (accept_3_2 25 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 152 (Polychromatic418967fa.accept_25_24_10_2_1_8165 24 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 152 (Polychromatic418967fa.accept_10_3_5_2_1_38 23 35 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 152 (accept_3_2 22 35 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 152
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 20 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 152 (accept_3_2 19 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 152 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 152 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 35 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 152 (accept_3_2 16 35 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 152
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 152 (accept_3_2 13 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 152 (Polychromatic418967fa.accept_15_12_5_2_1_2786 12 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 152 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 35 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 152 (accept_3_2 10 35 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 152
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 152 (accept_3_2 7 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  152 (Polychromatic418967fa.accept_20_6_15_12_1_6637 6 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 35 152 (Polychromatic418967fa.accept_14_5_7_12_1_4006 5 35 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 152 (accept_3_2 4 35 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 152
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 152 (accept_3_2 1 35 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  152))))))))))))))))))))))))))))))))))) (allB_succ 34 152 (allA_of_3_0 34 34 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 152 (allA_succ_of_accept 32 33 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 33 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 152 (accept_3_2 31 33 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 30
  33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 152 (accept_3_2 28 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 152 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 152 (Polychromatic418967fa.accept_28_26_5_12_1_8164 26 33 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 152 (accept_3_2 25 33 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 152 (Polychromatic418967fa.accept_13_11_7_9_1_612 24 33 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 152 (accept_3_2 22 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 33 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 152 (accept_3_2 19 33 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 33 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 152 (accept_3_2 16 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 152 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 33 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 152 (accept_3_2 13 33 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 152 (accept_3_2 10 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 152 (Polychromatic418967fa.accept_16_9_1_8_1_5766 9 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 152 (Polychromatic418967fa.accept_13_8_7_9_1_611 8 33 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 152 (accept_3_2 7 33 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 33 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 152
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 152 (accept_3_2 4 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  152 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 33 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 152 (accept_3_2 1 33 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 152))))))))))))))))))))))))))))))))) (allB_succ 32 152 (allA_succ_of_accept 31 32 152
  (accept_3_2 31 32 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 152 2 15 16 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 32 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 152 4 7 8 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 152 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 32 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 152 2 13 16 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 152 (accept_3_2 25 32 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 152 8 3 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 32 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 32 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 152 2 11 16 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 152
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 32 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 152 4 5 8 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 152 (accept_3_2 19 32 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  152 2 9 16 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 152 (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 32 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 152 8 2 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 152 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 32 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 152 2 7 16 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 152 (accept_3_2 13 32 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 152 4 3 8 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 152 2 5 16 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 152
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 32 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 152 8 1 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 152 (accept_3_2 7 32 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 152
  2 3 16 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  152 (Polychromatic418967fa.accept_18_5_14_8_1_2966 5 32 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 32 152 4 1 8 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 32 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 32 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 152 2 1 16 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 152 (accept_3_2 1 32 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 152)))))))))))))))))))))))))))))))) (allB_succ 31 152 (allA_of_3_0 31 31 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 152 (allA_succ_of_accept 29 30 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 152 2 14 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 152 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 30 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 152 2 13 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 152 (accept_3_2 25 30 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 152 2 12 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 152 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 152 2 11 15 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 152
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 30 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 152 2 10 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 152 (accept_3_2 19 30 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30
  152 2 9 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  30 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 30 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 152 2 8 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 30 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 152 2 7 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 152 (accept_3_2 13 30 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 152 2 6 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 30 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 30 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 152 2 5 15 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 152
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 152 2 4 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 152 (accept_3_2 7 30 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 152
  2 3 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30
  152 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 30 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 152 2 2 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 30 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 30 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 152 2 1 15 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 152 (accept_3_2 1 30 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 152)))))))))))))))))))))))))))))) (allB_succ 29 152 (allA_succ_of_accept 28 29 152
  (accept_3_2 28 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 152
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 152 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 29 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 152 (accept_3_2 25 29 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  29 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 152 (accept_3_2 22 29
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 152 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 152
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 152 (accept_3_2 19 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 152 (accept_3_2 16 29 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 152 (accept_3_2 13 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 152 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 29 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 152 (accept_3_2 10 29 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 152
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 152 (accept_3_2 7 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  152 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 29 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 152 (accept_3_2 4 29 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 152 (Polychromatic418967fa.accept_11_2_7_9_1_890 2
  29 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 152 (accept_3_2 1 29 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 152))))))))))))))))))))))))))))) (allB_succ 28 152 (allA_of_3_0
  28 28 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 152 (allA_succ_of_accept 26 27 152
  (Polychromatic418967fa.accept_17_9_10_16_1_3217 26 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 152 (accept_3_2 25 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 152 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 152 (accept_3_2 22 27 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 152 (Polychromatic418967fa.accept_13_8_1_9_1_1178 21 27 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 152
  (Polychromatic418967fa.accept_14_6_13_12_1_810 20 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 152 (accept_3_2 19 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 152 (accept_3_2 16 27 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 152
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 152 (accept_3_2 13 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 152 (Polychromatic418967fa.accept_16_12_11_8_1_832 12 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 152 (accept_3_2 10 27 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 152 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 27 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 152
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 152 (accept_3_2 7 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  152 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 152 (accept_3_2 4 27 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 152 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 27 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 152 (Polychromatic418967fa.accept_13_2_1_9_1_1174 2
  27 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 152 (accept_3_2 1 27 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 152))))))))))))))))))))))))))) (allB_succ 26 152
  (allA_succ_of_accept 25 26 152 (accept_3_2 25 26 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  152 2 12 13 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 152 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 26 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 152 2 11 13 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 152 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 26 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 152 2 10 13 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 152 (accept_3_2 19 26 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 152 2 9 13 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  26 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 152 2 8 13 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 152
  (Polychromatic418967fa.accept_20_15_6_12_1_2446 15 26 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 152 2 7 13 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 152 (accept_3_2 13 26 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  152 2 6 13 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 152 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 26 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 152 2 5 13 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 152 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 26 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 152 2 4 13 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 152 (accept_3_2 7 26 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 152 2 3 13 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 152 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 26 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 152 2 2 13 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 152
  (Polychromatic418967fa.accept_24_3_2_8_1_4572 3 26 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 152 2 1 13 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 152 (accept_3_2 1 26 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  152)))))))))))))))))))))))))) (allB_succ 25 152 (allA_of_3_0 25 25 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 152 (allA_succ_of_accept 23 24 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 152 2 11 12 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 152
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 152 4 5 6 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 152 (accept_3_2 19 24 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  152 2 9 12 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 152 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 24 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 152 8 2 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 152 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 152 2 7 12 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 152 (accept_3_2 13 24 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 152 4 3 6 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 152 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 152 2 5 12 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 152 8 1 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 152 (accept_3_2 7 24 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 152
  2 3 12 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  152 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 152 4 1 6 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 152 2 1 12 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 152 (accept_3_2 1 24 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 152)))))))))))))))))))))))) (allB_succ 23 152 (allA_succ_of_accept 22 23 152 (accept_3_2 22
  23 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 152
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 152 (accept_3_2 19 23 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 23 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  23 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 152 (accept_3_2 16 23
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 152 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 152
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 152 (accept_3_2 13 23 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 152 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 152 (accept_3_2 10 23 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 152
  (Polychromatic418967fa.accept_21_8_2_5_1_8163 8 23 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 152 (accept_3_2 7 23 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  152 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 23 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 152 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 23 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 152 (accept_3_2 4 23 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 152 (accept_3_2 1 23 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 152))))))))))))))))))))))) (allB_succ 22 152 (allA_of_3_0 22 22
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 152 (allA_succ_of_accept 20 21 152
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 21 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 152 (accept_3_2 19 21 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 152 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 152 (accept_3_2 16 21 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 152 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 21 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 152 (accept_3_2 13 21 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 152 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 21 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 152 (accept_3_2 10 21 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 152 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 21 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 152
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 21 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 152 (accept_3_2 7 21 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  152 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 152 (accept_3_2 4 21 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 152 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 21 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  21 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 152 (accept_3_2 1 21 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 152))))))))))))))))))))) (allB_succ 20 152 (allA_succ_of_accept
  19 20 152 (accept_3_2 19 20 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 152 2 9 10 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 152
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 20 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 152 4 4 5 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 152 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 20 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 152 2 7 10 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 152 (accept_3_2 13 20 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 152 4 3 5 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 152 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 20 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 152 2 5 10 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 152 (Polychromatic418967fa.accept_16_9_4_8_1_2533 9
  20 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 152 4 2 5 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 152 (accept_3_2 7 20
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 152 2 3 10 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 152
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 20 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 152 4 1 5 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 152 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 20 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 152 2 1 10 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 152 (accept_3_2 1 20 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 152)))))))))))))))))))) (allB_succ 19 152 (allA_of_3_0 19 19 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 152 (allA_succ_of_accept 17 18 152 (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 18 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 152 2 8 9 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 18 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 152 2 7 9 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 152 (accept_3_2 13 18 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  152 2 6 9 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 152 (Polychromatic418967fa.accept_21_11_18_5_1_8162 11 18 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 152 2 5 9 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 152 2 4 9 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 152 (accept_3_2 7 18 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 152 2 3 9 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 152 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 18 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 152 2 2 9 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 152
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 18 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 152 2 1 9 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 152 (accept_3_2 1 18 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  152)))))))))))))))))) (allB_succ 17 152 (allA_succ_of_accept 16 17 152 (accept_3_2 16 17 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 152
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 17 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 152 (accept_3_2 13 17 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 152 (Polychromatic418967fa.accept_16_12_1_8_1_5767 12 17 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 152 (Polychromatic418967fa.accept_21_11_17_5_1_8161 11 17 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 152 (accept_3_2 10 17 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 152
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 17 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 152 (accept_3_2 7 17 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  152 (Polychromatic418967fa.accept_13_6_4_9_1_4326 6 17 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 152 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 17 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 152 (accept_3_2 4 17 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 152
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 17 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 152 (accept_3_2 1 17 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  152))))))))))))))))) (allB_succ 16 152 (allA_of_3_0 16 16 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  152 (allA_succ_of_accept 14 15 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 15 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 152 (accept_3_2 13 15 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 15 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  15 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 152 (accept_3_2 10 15
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 152
  (Polychromatic418967fa.accept_16_9_15_8_1_3425 9 15 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 152 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 15 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 152 (accept_3_2 7 15 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 152 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 15 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 152 (accept_3_2 4 15 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 152
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 15 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 152 (accept_3_2 1 15 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  152))))))))))))))) (allB_succ 14 152 (allA_succ_of_accept 13 14 152 (accept_3_2 13 14 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 14 152 2 6 7 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 14 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 152 2 5 7 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 152 (Polychromatic418967fa.accept_21_9_14_5_1_8160 9
  14 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 152 2 4 7 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 152 (accept_3_2 7 14
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 152 2 3 7 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 152
  (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 152 2 2 7 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 152 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 14 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 152 2 1 7 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 152 (accept_3_2 1 14 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 152)))))))))))))) (allB_succ 13 152 (allA_of_3_0 13 13 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 152 (allA_succ_of_accept 11 12 152 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 12 152
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 152 2 5 6 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 152
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 12 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 152 4 2 3 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 152 (accept_3_2 7 12 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 152
  2 3 6 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 152
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 152 4 1 3 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 12 152 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 12 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 152 2 1 6 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 152 (accept_3_2 1 12 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 152)))))))))))) (allB_succ 11 152 (allA_succ_of_accept 10 11 152 (accept_3_2 10 11 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 152
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 11 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 152 (accept_3_2 7 11 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  152 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 11 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 152 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 11 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 152 (accept_3_2 4 11 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 152 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 152 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  11 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 152 (accept_3_2 1 11 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 152))))))))))) (allB_succ 10 152 (allA_of_3_0 10 10 152 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 152 (allA_succ_of_accept 8 9 152
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 9 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 152 (accept_3_2 7 9 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 152
  (Polychromatic418967fa.accept_12_6_9_8_1_165 6 9 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 152 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 152 (accept_3_2 4 9 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 152 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 152 (Polychromatic418967fa.accept_20_2_9_12_1_2546 2
  9 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 152 (accept_3_2 1 9 152
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 152))))))))) (allB_succ 8 152 (allA_succ_of_accept 7 8 152
  (accept_3_2 7 8 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 152 2 3 4 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 152
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 8 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 152 4 1 2 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 152 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 8 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 152 2 1 4 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 152 (accept_3_2 1 8 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 152)))))))) (allB_succ 7 152 (allA_of_3_0 7 7 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 152 (allA_succ_of_accept 5 6 152 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 152 2 2 3 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 152 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 6
  152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 152 2 1 3 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 152 (accept_3_2 1 6
  152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 152)))))) (allB_succ 5 152 (allA_succ_of_accept 4 5 152
  (accept_3_2 4 5 152 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 152
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 152 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 152 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 152 (accept_3_2 1 5 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 152))))) (allB_succ 4 152 (allA_of_3_0 4 4 152 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 152 (allA_succ_of_accept 2 3 152 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 3 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 152 (accept_3_2 1 3 152 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 3 152))) (allB_succ 2 152 (allA_succ_of_accept 1 2 152 (accept_3_2 1 2 152 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 2 152)) (allB_two
  152))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


