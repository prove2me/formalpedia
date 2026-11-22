-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch159
-- name    : Polychromatic418967fa_Branch159
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:15:49.403664+00:00
-- url     : https://prove2.me/theorems/6df166a1-8481-491e-9640-04ce37883a0c
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch159_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_159 : allB 159 159 :=
  allB_succ' 2 158 159 (Eq.refl Bool.true) (allA_succ_of_accept 1 158 159 (accept_3_4 1 158 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 158 159)) (allB_succ' 3 157 159 (Eq.refl Bool.true) (allA_succ_of_accept 2 157 159
  (accept_3_5 2 157 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 159
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 157 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 157 159))) (allB_succ' 4 156 159 (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 159 3 1 52 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 156 159
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 156 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 156 159 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 156 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156 159)))) (allB_succ' 5 155 159 (Eq.refl Bool.true) (allA_succ_of_accept 4
  155 159 (accept_3_4 4 155 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 159
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 155 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 155 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 155 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 159 (accept_3_4 1 155 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 155 159))))) (allB_succ' 6 154 159 (Eq.refl Bool.true) (allA_succ_of_accept 5 154 159
  (accept_3_5 5 154 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 159
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 154 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 154 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 154 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 159 (accept_3_5 2 154 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 154 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 159)))))) (allB_succ' 7 153 159 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 153 159 3 2 51 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 153 159 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 153 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 159 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 153 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 159 3 1 51 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 159
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 153 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153 159))))))) (allB_succ' 8 152 159 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 159 (accept_3_4 7 152 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 159 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 152 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 152 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 159 (accept_3_4 4 152 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 152 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 159
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 152 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 159 (accept_3_4 1 152 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  159)))))))) (allB_succ' 9 151 159 (Eq.refl Bool.true) (allA_succ_of_accept 8 151 159 (accept_3_5 8 151 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 159 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 151 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 159
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 151 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 159 (accept_3_5 5 151 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 159 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 151 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 159 (accept_3_5 2 151 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 159 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 151 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 159))))))))) (allB_succ' 10 150 159 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 150 159 3 3 50 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 150 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 150 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 159 (Polychromatic418967fa.accept_16_7_6_15_1_495
  7 150 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 159 3 2 50 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 150 159 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 150 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 150 159 3 1 50 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 150 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 150 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 159)))))))))) (allB_succ' 11 149 159 (Eq.refl Bool.true) (allA_succ_of_accept 10 149 159 (accept_3_4 10
  149 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 159
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 149 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 149 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 159 (accept_3_4 7 149 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 149 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 159 (Polychromatic418967fa.accept_13_5_6_3_1_868 5
  149 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 159 (accept_3_4 4 149
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 159
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 149 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 149 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 159 (accept_3_4 1 149 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 149 159))))))))))) (allB_succ' 12 148 159 (Eq.refl Bool.true) (allA_succ_of_accept 11 148 159
  (accept_3_5 11 148 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 159
  (Polychromatic418967fa.accept_7_3_1_5_1_44 10 148 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 148 159 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 148 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 159 (accept_3_5 8 148 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 148 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 159 (Polychromatic418967fa.accept_7_6_1_5_1_322 6
  148 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 159 (accept_3_5 5 148
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 159
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 148 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 148 159 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 148 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 159 (accept_3_5 2 148 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 148 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 159)))))))))))) (allB_succ' 13 147 159 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 147 159 3 4 49 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 147 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 147 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 159 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 147 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 159 3 3 49 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 159
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 147 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 159 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 147 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 159 3 2 49 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 159 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 147 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 159
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 147 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 159 3 1 49 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 147 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 159 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 147 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 159))))))))))))) (allB_succ' 14 146 159
  (Eq.refl Bool.true) (allA_succ_of_accept 13 146 159 (accept_3_4 13 146 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 146 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 146 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 146 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 159 (accept_3_4 10 146 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  146 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 159
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 146 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 159 (accept_3_4 7 146 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 159 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 146 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 159 (accept_3_4 4 146 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 146 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 159
  (Polychromatic418967fa.accept_15_2_11_9_1_263 2 146 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 159 (accept_3_4 1 146 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  159)))))))))))))) (allB_succ' 15 145 159 (Eq.refl Bool.true) (allA_succ_of_accept 14 145 159 (accept_3_5 14 145 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 159 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 145 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 159
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 145 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 159 (accept_3_5 11 145 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 145 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 159 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 145 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 159 (accept_3_5 8 145 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 159 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 145 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 159
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 159 (accept_3_5 5 145 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 145 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 159 (accept_3_5 2 145 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 159 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 145 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 159))))))))))))))) (allB_succ' 16 144 159 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 144 159 3 5 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 144 159 (Polychromatic418967fa.accept_17_14_8_6_1_2643 14 144 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 159
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 144 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 159 3 4 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 144 159 (Polychromatic418967fa.accept_13_11_1_3_1_910 11 144 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 159 (Polychromatic418967fa.accept_25_10_19_9_1_8739 10 144
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 144 159 3 3 48 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 144 159
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 144 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 144 159 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 144 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 159 3 2 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 159 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 144 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 159
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 4 144 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 144 159 3 1 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 144 159 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 144 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 159 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 144 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 159)))))))))))))))) (allB_succ' 17 143 159
  (Eq.refl Bool.true) (allA_succ_of_accept 16 143 159 (accept_3_4 16 143 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 143 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 143 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 143 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 159 (accept_3_4 13 143 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 12
  143 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 159
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 143 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 159 (accept_3_4 10 143 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 143 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 143 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 159 (accept_3_4 7 143 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 159 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 143 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 159
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 143 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 159 (accept_3_4 4 143 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 143 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 143 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 159 (accept_3_4 1 143 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 159))))))))))))))))) (allB_succ' 18 142 159 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 159 (accept_3_5 17 142 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 159 (Polychromatic418967fa.accept_15_1_7_9_1_20 16 142 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 159 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 142 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 159 (accept_3_5 14 142 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 159
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 142 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 159 (accept_3_5 11 142 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 142 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 159 (accept_3_5 8 142 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 142 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 159
  (Polychromatic418967fa.accept_11_6_10_5_1_341 6 142 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 159 (accept_3_5 5 142 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 159 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 142 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 142 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 159 (accept_3_5 2 142 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 159)))))))))))))))))) (allB_succ' 19 141 159
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 141 159 3 6 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 141 159 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 141 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 159
  (Polychromatic418967fa.accept_15_1_6_9_1_254 16 141 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 141 159 3 5 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 141 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 159 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 141 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 159 3 4 47 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 159
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 141 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 159 3 3 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 159 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 141 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 159
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 141 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 141 159 3 2 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 159 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 141 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 159 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 141 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 159 3 1 47 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 159
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 159 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 141 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141 159))))))))))))))))))) (allB_succ' 20 140 159 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 140 159 (accept_3_4 19 140 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 140 159 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 140 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 140 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 140 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 159 (accept_3_4 16 140 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 140 159 (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 140 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 140 159
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 140 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 140 159 (accept_3_4 13 140 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 140 159 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 140 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 140 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 159 (accept_3_4 10 140 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 159 (Polychromatic418967fa.accept_23_9_2_21_1_5246 9 140 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 159
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 140 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 140 159 (accept_3_4 7 140 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  140 159 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 140 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 140 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 159 (accept_3_4 4 140 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 159 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 140 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 159
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 140 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 159 (accept_3_4 1 140 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  159)))))))))))))))))))) (allB_succ' 21 139 159 (Eq.refl Bool.true) (allA_succ_of_accept 20 139 159 (accept_3_5 20 139
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 159 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 139 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 159
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 139 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 159 (accept_3_5 17 139 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 139 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 139 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 159 (accept_3_5 14 139 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 159 (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 139 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 159
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 139 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 159 (accept_3_5 11 139 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 139 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 159 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 139 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 159 (accept_3_5 8 139 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 159 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 139 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 159
  (Polychromatic418967fa.accept_13_6_9_3_1_915 6 139 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 159 (accept_3_5 5 139 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 159 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 139 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 159 (accept_3_5 2 139 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 139 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 159))))))))))))))))))))) (allB_succ' 22 138 159
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 159 3 7 46 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 138 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 138 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 159
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 138 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 159 3 6 46 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 159 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 138 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 138 159 3 5 46 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 138 159
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 138 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 159 3 4 46 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  138 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 159
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 138 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 138 159 3 3 46 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 138 159 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 138 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 159 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 138 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 159 3 2 46 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 159 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 138 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 138 159 3 1 46 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 138 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 138 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 159)))))))))))))))))))))) (allB_succ' 23 137 159 (Eq.refl Bool.true) (allA_succ_of_accept 22 137 159
  (accept_3_4 22 137 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 159
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 137 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 137 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 137 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 159 (accept_3_4 19 137 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 137 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 159 (Polychromatic418967fa.accept_9_8_2_6_1_875
  17 137 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 159 (accept_3_4 16
  137 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 159
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 137 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 137 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 159 (accept_3_4 13 137 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 137 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 137 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 159 (Polychromatic418967fa.accept_13_11_7_3_1_894
  11 137 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 159 (accept_3_4 10
  137 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 159
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 137 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 137 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 159 (accept_3_4 7 137 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 137 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 159 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  137 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 159 (accept_3_4 4 137
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 159
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 137 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 137 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 159 (accept_3_4 1 137 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 137 159))))))))))))))))))))))) (allB_succ' 24 136 159 (Eq.refl Bool.true) (allA_succ_of_accept
  23 136 159 (accept_3_5 23 136 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 136 159
  (Polychromatic418967fa.accept_7_1_3_5_1_33 22 136 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 136 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 136 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 159 (accept_3_5 20 136 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 136 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 136 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 159 (Polychromatic418967fa.accept_12_6_4_3_1_361
  18 136 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 159 (accept_3_5 17
  136 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 136 159
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 136 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 136 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 136 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 159 (accept_3_5 14 136 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 136 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 136 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  136 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 159 (accept_3_5 11
  136 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 159
  (Polychromatic418967fa.accept_11_10_4_5_1_359 10 136 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 136 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 136 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 159 (accept_3_5 8 136 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 136 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 159 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  136 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 159 (accept_3_5 5 136
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 159
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 136 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 136 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 136 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 159 (accept_3_5 2 136 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 136 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 159)))))))))))))))))))))))) (allB_succ' 25 135 159 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 135 159 3 8 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 135 159 (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 135 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 159
  (Polychromatic418967fa.accept_13_9_5_3_1_428 22 135 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 135 159 3 7 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 135 159 (Polychromatic418967fa.accept_19_1_2_7_1_2054 20 135 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 159 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 135
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 159 3 6 45 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 159
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 135 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 159 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 135 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 159 3 5 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 159 (Polychromatic418967fa.accept_10_4_5_9_1_1231
  14 135 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 159
  (Polychromatic418967fa.accept_19_13_2_7_1_8738 13 135 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 135 159 3 4 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 135 159 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 135 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 135 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 159 3 3 45 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 159
  (Polychromatic418967fa.accept_11_8_3_5_1_355 8 135 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 159 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 135 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 159 3 2 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 159 (Polychromatic418967fa.accept_18_5_9_15_1_4695 5 135 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 159
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 135 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 135 159 3 1 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 135 159 (Polychromatic418967fa.accept_13_2_5_3_1_406 2 135 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 159 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 135 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 159))))))))))))))))))))))))) (allB_succ' 26
  134 159 (Eq.refl Bool.true) (allA_succ_of_accept 25 134 159 (accept_3_4 25 134 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 134 159 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 134 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  134 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 159 (accept_3_4 22
  134 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 134 159 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 134 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 159 (accept_3_4 19 134 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 134 159 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 134 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 134 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  134 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 159 (accept_3_4 16
  134 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 159
  (Polychromatic418967fa.accept_10_5_4_9_1_420 15 134 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 134 159 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 134 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 159 (accept_3_4 13 134 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 134 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 134 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  134 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 159 (accept_3_4 10
  134 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 134 159 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 134 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 159 (accept_3_4 7 134 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 134 159 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 134 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  134 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 159 (accept_3_4 4 134
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 159 (Polychromatic418967fa.accept_7_3_1_5_1_44
  3 134 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 159
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 134 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 159 (accept_3_4 1 134 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  159)))))))))))))))))))))))))) (allB_succ' 27 133 159 (Eq.refl Bool.true) (allA_succ_of_accept 26 133 159 (accept_3_5
  26 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 159
  (Polychromatic418967fa.accept_17_8_14_6_1_8727 25 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 133 159 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 133 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 159 (accept_3_5 23 133 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 133 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 159 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  133 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 159 (accept_3_5 20
  133 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 159
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 133 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 159 (accept_3_5 17 133 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 133 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 133 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 159
  (Polychromatic418967fa.accept_17_15_14_6_1_7354 15 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 133 159 (accept_3_5 14 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 133 159 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 133 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 159 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 133 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 159 (accept_3_5 11 133 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  133 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 159
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 159 (accept_3_5 8 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 159 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 159 (accept_3_5 5 133 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 159
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 159 (accept_3_5 2 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 159 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 133 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 159))))))))))))))))))))))))))) (allB_succ' 28 132 159 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 132 159 3 9 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 132 159 (Polychromatic418967fa.accept_21_5_6_12_1_7091 26 132 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 159 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 132 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 159 3 8 44 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 159
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 132 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 132 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 132 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 132 159 3 7 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 132 159 (Polychromatic418967fa.accept_15_5_12_9_1_2253
  20 132 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 159
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 132 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 159 3 6 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 159 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 132 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 159 (Polychromatic418967fa.accept_18_16_6_15_1_3376 16 132
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 132 159 3 5 44 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 132 159
  (Polychromatic418967fa.accept_13_1_2_3_1_911 14 132 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 159 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 132 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 159 3 4 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 159 (Polychromatic418967fa.accept_7_4_6_5_1_141 11
  132 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 159
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 10 132 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 132 159 3 3 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 132 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 132 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 159 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 132 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 159 3 2 44 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 159
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 132 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 132 159 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 132 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 132 159 3 1 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 132 159 (Polychromatic418967fa.accept_17_2_13_6_1_3772 2 132 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 159
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 132 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 159)))))))))))))))))))))))))))) (allB_succ' 29 131 159 (Eq.refl Bool.true) (allA_succ_of_accept 28 131
  159 (accept_3_4 28 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 159
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 131 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 159 (accept_3_4 25 131 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 159 (Polychromatic418967fa.accept_13_11_1_3_1_910 24 131 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 159
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 23 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 159 (accept_3_4 22 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 159 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 131 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 159 (accept_3_4 19 131 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 159 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 131 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 159
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 159 (accept_3_4 16 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 159 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 131 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 159 (accept_3_4 13 131 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 159 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 131 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 159
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 159 (accept_3_4 10 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 159 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 159 (accept_3_4 7 131 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 159 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 131 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 159
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 159 (accept_3_4 4 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 159 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 131 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 131 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 159 (accept_3_4 1 131 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 159))))))))))))))))))))))))))))) (allB_succ' 30 130 159 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 130 159 (accept_3_5 29 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 130 159 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 130 159 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 130 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 130 159 (accept_3_5 26 130 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 130 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 130 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 130 159
  (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 130 159 (accept_3_5 23 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 130 159 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 130 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 130 159 (accept_3_5 20 130 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 130 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 130 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 159
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 130 159 (accept_3_5 17 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 130 159 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 130 159 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 130 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 159 (accept_3_5 14 130 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 130 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 159
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 159 (accept_3_5 11 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 130 159 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 130 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 159 (accept_3_5 8 130 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 130 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 159
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 159 (accept_3_5 5 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 159 (Polychromatic418967fa.accept_15_4_10_9_1_4298 4 130 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 159 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 130 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 159 (accept_3_5 2 130 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 159)))))))))))))))))))))))))))))) (allB_succ' 31 129
  159 (Eq.refl Bool.true) (allA_succ_of_gcd 30 129 159 3 10 43 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 129 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 159
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 129 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 129 159 3 9 43 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 129 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 159 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 129 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 159 3 8 43 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 159
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 129 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 159 3 7 43 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  129 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 159
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 129 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 129 159 3 6 43 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 129 159 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 129 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 129 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 159 3 5 43 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 159
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 159 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 129 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 159 3 4 43 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  129 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 159
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 129 159 3 3 43 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 129 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 129 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 159 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 129 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 159 3 2 43 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 159
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 129 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 159 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 129 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 159 3 1 43 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 159
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 129 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 129 159))))))))))))))))))))))))))))))) (allB_succ' 32 128 159 (Eq.refl Bool.true) (allA_succ_of_accept 31
  128 159 (accept_3_4 31 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 159
  (Polychromatic418967fa.accept_9_3_2_6_1_264 30 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 128 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 128 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 159 (accept_3_4 28 128 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 128 159 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 128 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 128 159
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 128 159 (accept_3_4 25 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 128 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 128 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 128 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 159 (accept_3_4 22 128 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 128 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 159
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 128 159 (accept_3_4 19 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 128 159 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 128 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 159 (accept_3_4 16 128 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 159 (Polychromatic418967fa.accept_13_2_11_3_1_873 15 128 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 159
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 128 159 (accept_3_4 13 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 128 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 159 (accept_3_4 10 128 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 159 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 128 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 159
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 159 (accept_3_4 7 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 159 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 159 (accept_3_4 4 128 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 128 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 159
  (Polychromatic418967fa.accept_13_2_11_3_1_873 2 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 159 (accept_3_4 1 128 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  159)))))))))))))))))))))))))))))))) (allB_succ' 33 127 159 (Eq.refl Bool.true) (allA_succ_of_accept 32 127 159
  (accept_3_5 32 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 159
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 127 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 127 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 159 (accept_3_5 29 127 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 127 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 127 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 159 (Polychromatic418967fa.accept_7_6_1_5_1_322
  27 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 159 (accept_3_5 26
  127 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 159
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 127 159 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 127 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 159 (accept_3_5 23 127 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 127 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 127 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 159 (accept_3_5 20
  127 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 159
  (Polychromatic418967fa.accept_13_6_10_3_1_897 19 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 127 159 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 127 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 159 (accept_3_5 17 127 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 127 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 159
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 159 (accept_3_5 14 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 159 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 127 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 159 (accept_3_5 11 127 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 127 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 159
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 159 (accept_3_5 8 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 159 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 159 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 127 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 159 (accept_3_5 5 127 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 159
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 159 (accept_3_5 2 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 159 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 127 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 159))))))))))))))))))))))))))))))))) (allB_succ' 34 126 159 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 126 159 3 11 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 126 159 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 126 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 159 (Polychromatic418967fa.accept_13_5_9_3_1_870
  31 126 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 159 3 10 42 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 126 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 126 159 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 126 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 126 159 3 9 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 126 159 (Polychromatic418967fa.accept_12_2_6_3_1_331
  26 126 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 159 3 8 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 126 159 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 126 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 159 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 126
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 126 159 3 7 42 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 159
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 126 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 159 (Polychromatic418967fa.accept_13_6_9_3_1_915 19 126 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 159 3 6 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  126 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 159
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 126 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 126 159 3 5 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 126 159 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 126 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 159 3 4 42 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 159
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 126 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 159 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 126 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 126 159 3 3 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 126 159 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 126 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 159
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 126 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 159 3 2 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 159 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 126 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 159 3 1 42 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 159
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 126 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 126 159)))))))))))))))))))))))))))))))))) (allB_succ' 35 125 159 (Eq.refl
  Bool.true) (allA_succ_of_accept 34 125 159 (accept_3_4 34 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 125 159 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 125 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 125 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 159 (accept_3_4 31 125 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 159
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 159 (accept_3_4 28 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 159 (Polychromatic418967fa.accept_15_12_5_9_1_3234 27 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 159 (accept_3_4 25 125 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 159 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 125 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 159
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 159 (accept_3_4 22 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 125 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 159 (accept_3_4 19 125 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 159
  (Polychromatic418967fa.accept_31_17_1_4_1_8737 17 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 159 (accept_3_4 16 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 159 (accept_3_4 13 125 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 125 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 159
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 159 (accept_3_4 10 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 159 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 159 (accept_3_4 7 125 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 159
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 159 (accept_3_4 4 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 125 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 159 (accept_3_4 1 125 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125 159))))))))))))))))))))))))))))))))))) (allB_succ' 36 124 159 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 159 (accept_3_5 35 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 124 159 (Polychromatic418967fa.accept_13_8_7_3_1_430 34 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 124 159 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 124 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 124 159 (accept_3_5 32 124 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 124 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 124 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 124 159
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 124 159 (accept_3_5 29 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 124 159 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 124 159 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 124 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 124 159 (accept_3_5 26 124 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 124 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 124 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 124 159
  (Polychromatic418967fa.accept_13_11_7_3_1_894 24 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 124 159 (accept_3_5 23 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 124 159 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 124 159 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 124 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 159 (accept_3_5 20 124 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 124 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 124 159
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 124 159 (accept_3_5 17 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 124 159 (Polychromatic418967fa.accept_19_16_10_7_1_8710 16 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 124 159 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 124 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 159 (accept_3_5 14 124 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 124 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 159
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 124 159 (accept_3_5 11 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 124 159 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 124 159 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 124 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 159 (accept_3_5 8 124 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 124 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 159
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 124 159 (accept_3_5 5 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  124 159 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 124 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 124 159 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 124 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 159 (accept_3_5 2 124 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 124 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 159)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 123 159 (Eq.refl Bool.true) (allA_succ_of_gcd 36 123 159 3 12 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 159 (Polychromatic418967fa.accept_13_9_6_3_1_1514
  35 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 159
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 159 3 11 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 159 (Polychromatic418967fa.accept_19_13_9_7_1_2038 32 123 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 159
  (Polychromatic418967fa.accept_13_5_6_3_1_868 31 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 159 3 10 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 159 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 123 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 159 (Polychromatic418967fa.accept_8_4_3_7_1_491
  28 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 159 3 9 41 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 159
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 159 (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 123 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 159 3 8 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 159 (Polychromatic418967fa.accept_7_2_4_5_1_313 23
  123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 159
  (Polychromatic418967fa.accept_7_1_4_5_1_35 22 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 123 159 3 7 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 123 159 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 123 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 159 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 123
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 159 3 6 41 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 159
  (Polychromatic418967fa.accept_16_1_11_15_1_498 17 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 159 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 123 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 159 3 5 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 159 (Polychromatic418967fa.accept_10_4_3_9_1_1262
  14 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 159
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 123 159 3 4 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 123 159 (Polychromatic418967fa.accept_17_11_4_6_1_2631 11 123 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 159 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 123
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 159 3 3 41 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 159
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 159 (Polychromatic418967fa.accept_16_7_11_15_1_2929 7 123 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 159 3 2 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 159 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 123 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 159
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 123 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 159 3 1 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 159 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 123 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 159 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 123 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 159)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 122 159 (Eq.refl Bool.true) (allA_succ_of_accept 37 122 159 (accept_3_4 37 122 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 122 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 159
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 122 159 (accept_3_4 34 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 122 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 122 159 (Polychromatic418967fa.accept_13_6_5_3_1_426 32 122 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 159 (accept_3_4 31 122 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 122 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 122 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 122 159 (accept_3_4 28 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 122 159 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 122 159 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 122 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 159 (accept_3_4 25 122 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 159 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 122 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 159
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 122 159 (accept_3_4 22 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 122 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 122 159 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 122 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 159 (accept_3_4 19 122 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 159 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 122 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 122 159 (accept_3_4 16 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 122 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 122 159 (Polychromatic418967fa.accept_13_1_5_3_1_888 14 122 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 159 (accept_3_4 13 122 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 159 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 122 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 159
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 122 159 (accept_3_4 10 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  122 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 122 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 122 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 159 (accept_3_4 7 122 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 159 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 122 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 122 159 (accept_3_4 4 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  122 159 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 122 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 122 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 122 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 159 (accept_3_4 1 122 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 122 159)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 121 159 (Eq.refl
  Bool.true) (allA_succ_of_accept 38 121 159 (accept_3_5 38 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 121 159 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 121 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 159 (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 121
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 159 (accept_3_5 35 121
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 159
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 121 159 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 121 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 159 (accept_3_5 32 121 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 121 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 121 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 159 (accept_3_5 29
  121 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 159
  (Polychromatic418967fa.accept_6_4_1_3_1_77 28 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 121 159 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 121 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 159 (accept_3_5 26 121 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 121 159 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 121 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 159 (Polychromatic418967fa.accept_7_3_2_5_1_147
  24 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 159 (accept_3_5 23
  121 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 159
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 121 159 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 121 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 159 (accept_3_5 20 121 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 121 159 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 121 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 159 (accept_3_5 17
  121 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 159
  (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 121 159 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 121 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 159 (accept_3_5 14 121 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 121 159 (Polychromatic418967fa.accept_17_13_2_6_1_3683 13 121 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 159
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 159 (accept_3_5 11 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 159 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 121 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 159 (accept_3_5 8 121 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 159 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 121 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 159
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 159 (accept_3_5 5 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 121 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 159 (accept_3_5 2 121 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 159 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 121 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 159)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 120 159 (Eq.refl Bool.true) (allA_succ_of_gcd 39 120 159 3 13 40 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 120 159
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 159 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 120 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 159 3 12 40 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 120 159 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 159
  (Polychromatic418967fa.accept_7_6_1_5_1_322 34 120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 120 159 3 11 40 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 120 159 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 120 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 159 (Polychromatic418967fa.accept_7_3_1_5_1_44 31
  120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 159 3 10 40 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 159
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 120 159 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 120 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 120 159 3 9 40 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 120 159 (Polychromatic418967fa.accept_9_8_3_6_1_533 26
  120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 159
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 159 3 8 40 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 159 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 120 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 159 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 120 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 120 159 3 7 40 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 120 159
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 159 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 120 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 159 3 6 40 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 159 (Polychromatic418967fa.accept_7_3_1_5_1_44 17
  120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 159
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 120 159 3 5 40 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 120 159 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 120 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 159 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 120 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 159 3 4 40 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 159
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 159 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 120 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 120 159 3 3 40 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 120 159 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 120 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 159
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 159 3 2 40 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 159 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 120 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 159 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 120 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 120 159 3 1 40 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 120 159
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 120 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 159 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 120 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120 159)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 119 159
  (Eq.refl Bool.true) (allA_succ_of_accept 40 119 159 (accept_3_4 40 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 119 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 119 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 119 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 159 (accept_3_4 37 119 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 159
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 119 159 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 119 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 159 (accept_3_4 34 119 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 119 159 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 119 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 159
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 159 (accept_3_4 31 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 159 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 119 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 159 (accept_3_4 28 119 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 159 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 119
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 159
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 159 (accept_3_4 25 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 159 (Polychromatic418967fa.accept_13_11_2_3_1_883 24 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 159 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 119 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 159 (accept_3_4 22 119 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 119 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 159
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 159 (accept_3_4 19 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 159 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 159 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 119 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 159 (accept_3_4 16 119 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 159 (Polychromatic418967fa.accept_21_15_14_12_1_8736 15 119 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 159
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 159 (accept_3_4 13 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 159 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 119 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 159 (accept_3_4 10 119 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 159 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 119 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 159
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 159 (accept_3_4 7 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 159 (Polychromatic418967fa.accept_15_6_14_9_1_1471 6 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 159 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 119 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 159 (accept_3_4 4 119 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 119 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 159
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 159 (accept_3_4 1 119 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  159))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 118 159 (Eq.refl Bool.true) (allA_succ_of_accept 41 118
  159 (accept_3_5 41 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 118 159
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 118 159 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 118 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 159 (accept_3_5 38 118 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 118 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 36
  118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 118 159 (accept_3_5 35
  118 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 118 159
  (Polychromatic418967fa.accept_9_7_1_6_1_261 34 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 118 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 159 (accept_3_5 32 118 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 118 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 118 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 30
  118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 118 159 (accept_3_5 29
  118 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 118 159
  (Polychromatic418967fa.accept_13_2_1_3_1_419 28 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 118 159 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 118 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 159 (accept_3_5 26 118 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 118 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 159 (Polychromatic418967fa.accept_10_4_8_9_1_784
  24 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 159 (accept_3_5 23
  118 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 159
  (Polychromatic418967fa.accept_7_1_6_5_1_39 22 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 118 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 159 (accept_3_5 20 118 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 118 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 118 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 159 (Polychromatic418967fa.accept_7_4_6_5_1_141
  18 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 159 (accept_3_5 17
  118 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 159
  (Polychromatic418967fa.accept_9_7_1_6_1_261 16 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 118 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 118 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 159 (accept_3_5 14 118 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 118 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 159 (accept_3_5 11
  118 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 159
  (Polychromatic418967fa.accept_17_10_16_6_1_4890 10 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 159 (accept_3_5 8 118 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 118 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 159
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 159 (accept_3_5 5 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 159 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 118 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 118 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 159 (accept_3_5 2 118 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 159))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 117 159 (Eq.refl Bool.true) (allA_succ_of_gcd 42 117 159 3 14 39 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 159
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 159 (Polychromatic418967fa.accept_15_10_12_9_1_776 40 117 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 159 3 13 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 159
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 159 3 12 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 117 159 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 117 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 159
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 117 159 3 11 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 117 159 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 117 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 159 (Polychromatic418967fa.accept_11_9_7_5_1_749
  31 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 159 3 10 39 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 159
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 159 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 117 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 159 3 9 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 159
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 117 159 3 8 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 117 159 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 117 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 159 3 7 39 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 159
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 159 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 117 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 159 3 6 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 159 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 159
  (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 117 159 3 5 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 117 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 159
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 117 159 3 4 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 117 159 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 117 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 159 3 3 39 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 159
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 159 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 117 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 159 3 2 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 159 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 117 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 159
  (Polychromatic418967fa.accept_15_4_12_9_1_773 4 117 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 117 159 3 1 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 117 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 159 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 117 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  159))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 116 159 (Eq.refl Bool.true) (allA_succ_of_accept 43 116
  159 (accept_3_4 43 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 159
  (Polychromatic418967fa.accept_12_6_8_3_1_82 42 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 116 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 116 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 159 (accept_3_4 40 116 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 116 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 116 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 159 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 159 (accept_3_4 37
  116 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 159
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 116 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 116 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 159 (accept_3_4 34 116 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 116 159 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 116 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 159
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 159 (accept_3_4 31 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 159 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 116 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 159 (accept_3_4 28 116 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 159 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 116 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 159
  (Polychromatic418967fa.accept_21_5_11_12_1_1479 26 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 116 159 (accept_3_4 25 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 116 159 (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 116 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 159 (accept_3_4 22 116 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 159
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 159 (accept_3_4 19 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 159 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 159 (accept_3_4 16 116 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 159 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 116 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 159
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 159 (accept_3_4 13 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 116 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 159 (accept_3_4 10 116 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 159 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 116 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 159
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 159 (accept_3_4 7 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 159 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 159 (accept_3_4 4 116 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 159 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 116 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 159
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 159 (accept_3_4 1 116 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  159)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 115 159 (Eq.refl Bool.true) (allA_succ_of_accept 44 115
  159 (accept_3_5 44 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 159
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 115 159 (Polychromatic418967fa.accept_15_12_10_9_1_798 42 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 159 (accept_3_5 41 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 115 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 115 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 159 (Polychromatic418967fa.accept_9_3_7_6_1_76 39
  115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 159 (accept_3_5 38
  115 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 159
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 115 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 159 (accept_3_5 35 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 115 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 115 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 159 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  33 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 159 (accept_3_5 32
  115 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 159
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 115 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 159 (accept_3_5 29 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 115 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 115 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 159 (Polychromatic418967fa.accept_13_1_11_3_1_901
  27 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 159 (accept_3_5 26
  115 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 159
  (Polychromatic418967fa.accept_19_6_1_7_1_5872 25 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 115 159 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 159 (accept_3_5 23 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 115 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 115 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 159 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 159 (accept_3_5 20
  115 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 159
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 159 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 159 (accept_3_5 17 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 159 (accept_3_5 14
  115 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 159
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 115 159 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 159 (accept_3_5 11 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 115 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 115 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 9
  115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 159 (accept_3_5 8 115
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 159
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 115 159 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 159 (accept_3_5 5 115 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 115 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 159 (Polychromatic418967fa.accept_9_3_7_6_1_76 3
  115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 159 (accept_3_5 2 115
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 159 (Polychromatic418967fa.accept_7_1_3_5_1_33
  1 115 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  159))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 114 159 (Eq.refl Bool.true) (allA_succ_of_gcd 45 114
  159 3 15 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  114 159 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 114 159 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 114 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 114 159 3 14 38 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 114 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 114 159 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 114 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 114 159 3 13 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 114 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 38
  114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 159 3 12 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 159 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 114 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 159 (Polychromatic418967fa.accept_12_10_6_3_1_786
  34 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 114 159 3 11 38 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 114 159
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 114 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 114 159 3 10 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 114 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 159
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 114 159 3 9 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 114 159 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 114 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 159 3 8 38 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 159
  (Polychromatic418967fa.accept_10_3_4_9_1_15 23 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 159 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 114 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 114 159 3 7 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 114 159 (Polychromatic418967fa.accept_12_8_6_3_1_366
  20 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 159
  (Polychromatic418967fa.accept_13_6_10_3_1_897 19 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 159 3 6 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 159 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 114
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 114 159 3 5 38 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 114 159
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 159 3 4 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 159 (Polychromatic418967fa.accept_7_4_2_5_1_527 11
  114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 159
  (Polychromatic418967fa.accept_7_3_2_5_1_147 10 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 114 159 3 3 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 114 159 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 114 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 159 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 114
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 159 3 2 38 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 159 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 114 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 114 159 3 1 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 114 159 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 114 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 114 159)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 113 159 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 113 159 (accept_3_4 46 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 159 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 159 (accept_3_4 43 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 159
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 159 (accept_3_4 40 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 159 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 159 (accept_3_4 37 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 159 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 113 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 159
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 159 (accept_3_4 34 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 159 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 159 (accept_3_4 31 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 159
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 159 (accept_3_4 28 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 159 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 159 (accept_3_4 25 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 159 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 113 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 159
  (Polychromatic418967fa.accept_22_1_3_5_1_375 23 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 159 (accept_3_4 22 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 159 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 159 (accept_3_4 19 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 159
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 159 (accept_3_4 16 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 159 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 159 (accept_3_4 13 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 159 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 113 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 159
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 159 (accept_3_4 10 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 159 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 159 (accept_3_4 7 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 159
  (Polychromatic418967fa.accept_13_5_9_3_1_870 5 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 159 (accept_3_4 4 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 159 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 113 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 159 (accept_3_4 1 113 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 159))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 112 159 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 112 159 (accept_3_5 47 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 112 159 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 112 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 159 (Polychromatic418967fa.accept_18_9_4_15_1_555 45 112
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 112 159 (accept_3_5 44 112
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 112 159
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 112 159 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 112 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 159 (accept_3_5 41 112 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 112 159 (Polychromatic418967fa.accept_19_2_17_7_1_8735 40 112 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 159
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 159 (accept_3_5 38 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 159 (Polychromatic418967fa.accept_21_15_7_12_1_8686 36 112 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 159 (accept_3_5 35 112 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 159 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 112 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 159
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 33 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 159 (accept_3_5 32 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 159 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 112 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 159 (accept_3_5 29 112 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 159 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 112 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 159
  (Polychromatic418967fa.accept_10_7_2_9_1_775 27 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 159 (accept_3_5 26 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 159 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 112 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 159 (accept_3_5 23 112 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 159 (Polychromatic418967fa.accept_13_9_8_3_1_3045 22 112
  159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 159
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 159 (accept_3_5 20 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 159 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 112 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 159 (accept_3_5 17 112 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 159 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 112 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 159
  (Polychromatic418967fa.accept_19_15_17_7_1_8734 15 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 112 159 (accept_3_5 14 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 112 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 159 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 112 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 159 (accept_3_5 11 112 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 159 (Polychromatic418967fa.accept_9_1_4_6_1_5 10
  112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 159
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 159 (accept_3_5 8 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 159 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 112 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 159 (accept_3_5 5 112 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 159 (Polychromatic418967fa.accept_17_4_10_6_1_4869 4 112 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 159
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 159 (accept_3_5 2 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 159 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112 159)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 111 159 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 111 159 3 16 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 111 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 111 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 159
  (Polychromatic418967fa.accept_7_4_6_5_1_141 46 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 159 3 15 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 159 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 111 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 43
  111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 159 3 14 37 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 159
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 159 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 111 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 159 3 13 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 159
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 159 3 12 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 159 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 111 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 159 (Polychromatic418967fa.accept_9_7_3_6_1_270
  34 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 111 159 3 11 37 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 159
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 159 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 111 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 159 3 10 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 29
  111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 159
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 111 159 3 9 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 111 159 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 111 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 159 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 111 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 159 3 8 37 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 159
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 111 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 159 3 7 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 159
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 111 159 3 6 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 111 159 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 111 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 159 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 111 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 159 3 5 37 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 159
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 159 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 111 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 159 3 4 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 159 (Polychromatic418967fa.accept_7_4_6_5_1_141 11
  111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 159
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 111 159 3 3 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 111 159 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 111 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 159 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 111 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 159 3 2 37 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 159
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 159 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 111 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 159 3 1 37 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 159 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 111 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 159
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 111 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 159))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 110 159 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 110 159 (accept_3_4 49 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 110 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 110 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 110 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 159 (accept_3_4 46 110 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 110 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 110 159
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 110 159 (accept_3_4 43 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 110 159 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 110 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 159 (accept_3_4 40 110 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 110 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 110 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 159
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 38 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 110 159 (accept_3_4 37 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 110 159 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 110 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 110 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 159 (accept_3_4 34 110 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 159
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 159 (accept_3_4 31 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 159 (accept_3_4 28 110 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 159 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 110 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 159
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 110 159 (accept_3_4 25 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 110 159 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 110 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 110 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 159 (accept_3_4 22 110 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 159
  (Polychromatic418967fa.accept_16_4_14_15_1_6331 20 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 110 159 (accept_3_4 19 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 110 159 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 110 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 159 (accept_3_4 16 110 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 159
  (Polychromatic418967fa.accept_17_15_8_6_1_8733 15 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 110 159 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 110 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 159 (accept_3_4 13 110 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 110 159 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 110 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 159 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 159 (accept_3_4 10
  110 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 159
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 110 159 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 110 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 159 (accept_3_4 7 110 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 110 159 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 110 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 159 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 159 (accept_3_4 4 110
  159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 159
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 110 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 110 159 (Polychromatic418967fa.accept_26_2_6_3_1_8732 2 110 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 159 (accept_3_4 1 110 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 110 159)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 109 159 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 109 159 (accept_3_5 50 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 109 159 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 109 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 159 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 109 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 159 (accept_3_5 47 109 159
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 159
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 159 (accept_3_5 44 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 159 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 159 (accept_3_5 41 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 109 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 159
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 159 (accept_3_5 38 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 159 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 159 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 159 (accept_3_5 35 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 159
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 159 (accept_3_5 32 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 159 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 159 (accept_3_5 29 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 109 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 159
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 159 (accept_3_5 26 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 159 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 159 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 109 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 159 (accept_3_5 23 109 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 159
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 159 (accept_3_5 20 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 159 (Polychromatic418967fa.accept_13_6_5_3_1_426 19 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 159 (accept_3_5 17 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 159
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 159 (accept_3_5 14 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 159 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 159 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 159 (accept_3_5 11 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 159
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 159 (accept_3_5 8 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 159 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 159 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 159 (accept_3_5 5 109 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 159 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 159
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 159 (accept_3_5 2 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 159 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 109 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 159))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 108 159 (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 108 159 3 17 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 108 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 108 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 159
  (Polychromatic418967fa.accept_19_11_13_7_1_5862 49 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 108 159 3 16 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 108 159 (Polychromatic418967fa.accept_10_7_8_9_1_785 47 108 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 159
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 46 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 108 159 3 15 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 108 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 108 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 43
  108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 108 159 3 14 36 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 108 159
  (Polychromatic418967fa.accept_10_1_8_9_1_787 41 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 159 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 108 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 108 159 3 13 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 108 159 (Polychromatic418967fa.accept_13_12_4_3_1_1528
  38 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 159
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 159 3 12 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 159 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 108 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 159 (Polychromatic418967fa.accept_10_4_8_9_1_784
  34 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 108 159 3 11 36 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 108 159
  (Polychromatic418967fa.accept_21_11_3_12_1_8695 32 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 108 159 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 108 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 159 3 10 36 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 159
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 159 (Polychromatic418967fa.accept_15_13_3_9_1_1482 28 108 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 108 159 3 9 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 108 159
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 26 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 108 159 (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 108 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 159 3 8 36 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 159
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 108 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 108 159 3 7 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 108 159 (Polychromatic418967fa.accept_13_7_4_3_1_3064
  20 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 159
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 159 3 6 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 159 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 108 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 108 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 108 159 3 5 36 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 108 159
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 159 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 108 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 159 3 4 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 159 (Polychromatic418967fa.accept_8_3_4_7_1_475 11
  108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 159
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 10 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 108 159 3 3 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 108 159 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 108 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 159 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 108 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 159 3 2 36 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 159
  (Polychromatic418967fa.accept_15_5_3_9_1_283 5 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 159 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 108 159 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 108 159 3 1 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 159 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 108 159
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 159
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 108 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 159)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 107 159 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 107 159 (accept_3_4 52 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 159 (Polychromatic418967fa.accept_16_3_11_15_1_1963 51 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 159 (accept_3_4 49 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 107 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 159
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 159 (accept_3_4 46 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 159 (accept_3_4 43 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 159 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 107 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 159
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 159 (accept_3_4 40 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 159 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 159 (accept_3_4 37 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 159 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 107 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 159
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 159 (accept_3_4 34 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 159 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 159 (accept_3_4 31 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 107 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 159
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 159 (accept_3_4 28 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 159 (Polychromatic418967fa.accept_18_9_17_15_1_2267 27 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 159 (accept_3_4 25 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 107 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 159
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 159 (accept_3_4 22 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 159 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 159 (accept_3_4 19 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 159 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 107 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 159
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 159 (accept_3_4 16 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 159 (Polychromatic418967fa.accept_19_15_12_7_1_7227 15 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 159 (accept_3_4 13 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 159 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 107 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 159
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 159 (accept_3_4 10 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 159 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 159 (accept_3_4 7 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 159 (Polychromatic418967fa.accept_18_6_17_15_1_4603 6 107 159 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 159
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 159 (accept_3_4 4 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 159 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 107 159 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 159 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 159 (accept_3_4 1 107 159 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 159)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_159_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))


