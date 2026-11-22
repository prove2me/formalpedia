-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch179
-- name    : Polychromatic418967fa_Branch179
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:21:03.561807+00:00
-- url     : https://prove2.me/theorems/7ab686cf-66b1-4fc8-ac5c-121d8df485bc
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

def Polychromatic418967fa.branch_179 : allB 179 179 :=
  allB_succ' 2 178 179 (Eq.refl Bool.true) (allA_of_3_0 2 178 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  177 179 (Eq.refl Bool.true) (allA_succ_of_accept 2 177 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 179 (accept_3_2 1 177 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 179))) (allB_succ' 4 176 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 176 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 176 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 176 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 176 179 (accept_3_2 1 176 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176 179)))) (allB_succ' 5 175 179 (Eq.refl Bool.true) (allA_of_3_0
  5 175 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 174 179 (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 174 179 (accept_3_2 4 174 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 174 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 174 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 174 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 179 (accept_3_2 1 174 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 179)))))) (allB_succ' 7 173 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 173 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 173 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 173 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 179 (accept_3_2 4 173 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  173 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 179 (accept_3_2 1 173 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173 179)))))))
  (allB_succ' 8 172 179 (Eq.refl Bool.true) (allA_of_3_0 8 172 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 171 179 (Eq.refl Bool.true) (allA_succ_of_accept 8 171 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 179 (accept_3_2 7 171 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  171 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 179
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 171 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 179 (accept_3_2 4 171 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 179 (Polychromatic418967fa.accept_13_3_2_10_1_2697 3 171 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 171 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 179 (accept_3_2 1 171 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 179))))))))) (allB_succ' 10 170 179 (Eq.refl Bool.true) (allA_succ_of_accept 9 170
  179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 170 179 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 170 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 179 (accept_3_2 7 170 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 170 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 170 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 170 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  170 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 179 (accept_3_2 4 170
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 179 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 170 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 179
  (Polychromatic418967fa.accept_15_2_5_14_1_61 2 170 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 179 (accept_3_2 1 170 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  179)))))))))) (allB_succ' 11 169 179 (Eq.refl Bool.true) (allA_of_3_0 11 169 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 168 179 (Eq.refl Bool.true) (allA_succ_of_accept 11 168 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 168 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 168 179 (accept_3_2 10 168 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  168 179 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 168 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 168 179 (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 168 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 179 (accept_3_2 7 168 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 168 179 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 168
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 168 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 179 (accept_3_2 4 168 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  168 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 168 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 168 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 168 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 179 (accept_3_2 1 168 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 168 179)))))))))))) (allB_succ' 13 167 179 (Eq.refl Bool.true) (allA_succ_of_accept 12
  167 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 167 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 167 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 179 (accept_3_2 10 167 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 167 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 179
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 167 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 179 (accept_3_2 7 167 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 167 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 167 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 179 (accept_3_2 4 167 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 167 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 167 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 179 (accept_3_2 1 167 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  179))))))))))))) (allB_succ' 14 166 179 (Eq.refl Bool.true) (allA_of_3_0 14 166 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 165 179 (Eq.refl Bool.true) (allA_succ_of_accept 14 165 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 165 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 179 (accept_3_2 13 165 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 165 179 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 165 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 165 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 165 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 179 (accept_3_2 10 165 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 179 (Polychromatic418967fa.accept_21_9_18_11_1_8644 9 165 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 179 (accept_3_2 7 165 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  165 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 165 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 165 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 179 (accept_3_2 4 165 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 165 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 179 (accept_3_2 1 165 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  179))))))))))))))) (allB_succ' 16 164 179 (Eq.refl Bool.true) (allA_succ_of_accept 15 164 179
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 164 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 164 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 164 179 (accept_3_2 13 164 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 164 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 164 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 179
  (Polychromatic418967fa.accept_13_11_8_10_1_676 11 164 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 164 179 (accept_3_2 10 164 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  164 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 164 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 164 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 179 (accept_3_2 7 164 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 164 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 164 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 164 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 164 179 (accept_3_2 4 164 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  164 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 164 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 164 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 179 (accept_3_2 1 164 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 179)))))))))))))))) (allB_succ' 17 163 179 (Eq.refl Bool.true) (allA_of_3_0 17 163
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 162 179 (Eq.refl Bool.true) (allA_succ_of_accept 17 162
  179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 162 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 179 (accept_3_2 16 162 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 162 179 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 162 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 162 179 (Polychromatic418967fa.accept_26_14_6_23_1_10134 14 162 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 179 (accept_3_2 13 162 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 162 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 162 179
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 162 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 179 (accept_3_2 10 162 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  162 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 162 179 (Polychromatic418967fa.accept_24_8_18_11_1_10133 8 162 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 179 (accept_3_2 7 162 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 179 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 162 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 179 (accept_3_2 4 162 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  162 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 162 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 162 179 (Polychromatic418967fa.accept_13_2_6_10_1_2703 2 162 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 179 (accept_3_2 1 162 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162 179)))))))))))))))))) (allB_succ' 19 161 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 161 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 179 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 161
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 179 (accept_3_2 16 161
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 179
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 161 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 161 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 161 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 179 (accept_3_2 13 161 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 161 179 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 161 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 179
  (Polychromatic418967fa.accept_17_11_8_9_1_8919 11 161 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 179 (accept_3_2 10 161 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 179 (Polychromatic418967fa.accept_24_9_17_11_1_4810 9 161 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 179 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 161 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 179 (accept_3_2 7 161 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 179
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 161 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 179 (accept_3_2 4 161 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 179 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 161 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 179 (accept_3_2 1 161 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 179))))))))))))))))))) (allB_succ' 20 160 179 (Eq.refl Bool.true) (allA_of_3_0 20
  160 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 159 179 (Eq.refl Bool.true) (allA_succ_of_accept 20
  159 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 159 179 (accept_3_2 19 159 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 159 179 (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 159 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 179 (Polychromatic418967fa.accept_22_17_5_3_1_5229 17 159
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 179 (accept_3_2 16 159
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 159 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 159 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 159 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 179 (accept_3_2 13 159 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 159 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 159 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 179 (Polychromatic418967fa.accept_9_2_6_8_1_321
  11 159 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 179 (accept_3_2 10
  159 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 159 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 179 (accept_3_2 7 159 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 159 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 5
  159 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 179 (accept_3_2 4 159
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 179
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 159 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 159 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 179 (accept_3_2 1 159 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 179))))))))))))))))))))) (allB_succ' 22 158 179 (Eq.refl Bool.true) (allA_succ_of_accept 21
  158 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 158 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 158 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 179 (accept_3_2 19 158 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 158 179 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 158 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 158 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 158 179 (accept_3_2 16 158 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 158 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 158 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 158 179 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 158 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 158 179 (accept_3_2 13 158 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 158 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 158 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 158 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 158 179 (accept_3_2 10 158 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  158 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 158 179 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 158 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 179 (accept_3_2 7 158 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 158 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 158 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 158 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 158 179 (accept_3_2 4 158 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  158 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 158 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 158 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 158 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 179 (accept_3_2 1 158 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 158 179)))))))))))))))))))))) (allB_succ' 23 157 179 (Eq.refl Bool.true) (allA_of_3_0
  23 157 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 156 179 (Eq.refl Bool.true) (allA_succ_of_accept 23
  156 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 156 179 (accept_3_2 22 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 156 179 (Polychromatic418967fa.accept_22_21_2_3_1_6962 21 156 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 156 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 179 (accept_3_2 19 156 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 179 (Polychromatic418967fa.accept_17_1_3_9_1_958
  18 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 156 179
  (Polychromatic418967fa.accept_19_17_4_8_1_4500 17 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 156 179 (accept_3_2 16 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 156 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 156 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 156 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 179 (accept_3_2 13 156 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 156 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 156 179 (accept_3_2 10 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  156 179 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 156 179 (Polychromatic418967fa.accept_15_8_6_14_1_975 8 156 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 179 (accept_3_2 7 156 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 156 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 156 179 (accept_3_2 4 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  156 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 156 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 156 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 156 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 179 (accept_3_2 1 156 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 156 179)))))))))))))))))))))))) (allB_succ' 25 155 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 24 155 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 155 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 155 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 179 (accept_3_2 22 155 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 179 (Polychromatic418967fa.accept_9_3_2_8_1_108
  21 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 179
  (Polychromatic418967fa.accept_13_7_12_10_1_640 20 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 179 (accept_3_2 19 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 179 (Polychromatic418967fa.accept_14_4_1_11_1_5026 18 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 155 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 179 (accept_3_2 16 155 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 155 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 179 (accept_3_2 13 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 179 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 155 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 179 (accept_3_2 10 155 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 179 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 155
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 179
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 179 (accept_3_2 7 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 155 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 179 (accept_3_2 4 155 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 155 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 179
  (Polychromatic418967fa.accept_11_2_1_3_1_683 2 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 179 (accept_3_2 1 155 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  179))))))))))))))))))))))))) (allB_succ' 26 154 179 (Eq.refl Bool.true) (allA_of_3_0 26 154 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 153 179 (Eq.refl Bool.true) (allA_succ_of_accept 26 153 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 179 (accept_3_2 25 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 153 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 153 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 179 (accept_3_2 22 153 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 179 (Polychromatic418967fa.accept_19_2_1_8_1_7279 21 153 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 179 (accept_3_2 19 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 153 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 153 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 153 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 179 (accept_3_2 16 153 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 153 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 179 (accept_3_2 13 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 179 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 153 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 179 (accept_3_2 10 153 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 153 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 179 (accept_3_2 7 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 153 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 179 (accept_3_2 4 153 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 153 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 179 (accept_3_2 1 153 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  179))))))))))))))))))))))))))) (allB_succ' 28 152 179 (Eq.refl Bool.true) (allA_succ_of_accept 27 152 179
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 152 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 152 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 152 179 (accept_3_2 25 152 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 152 179 (Polychromatic418967fa.accept_22_2_20_3_1_8618 24 152 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 152 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 152 179 (accept_3_2 22 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 152 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 152 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 152 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 179 (accept_3_2 19 152 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 152 179 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 152 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 152 179
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 152 179 (accept_3_2 16 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 152 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 152 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 152 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 179 (accept_3_2 13 152 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 152 179 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 152
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 152 179
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 152 179 (accept_3_2 10 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  152 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 152 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 152 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 179 (accept_3_2 7 152 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 152 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 152 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 152 179
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 152 179 (accept_3_2 4 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  152 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 152 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 152 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 179 (accept_3_2 1 152 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 179)))))))))))))))))))))))))))) (allB_succ' 29 151 179 (Eq.refl Bool.true)
  (allA_of_3_0 29 151 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 150 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 150 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 150 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 179 (accept_3_2 28 150 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 150 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 179 (Polychromatic418967fa.accept_11_4_7_3_1_289
  26 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 179 (accept_3_2 25
  150 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 179
  (Polychromatic418967fa.accept_26_24_20_23_1_10132 24 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 150 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 179 (accept_3_2 22 150 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 179
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 150 179 (accept_3_2 19 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 150 179 (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 150 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 179 (accept_3_2 16 150 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 150 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 150 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 150 179 (accept_3_2 13 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 150 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 150 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 150 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 179 (accept_3_2 10 150 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 150 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 179 (accept_3_2 7 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  150 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 150 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 179 (accept_3_2 4 150 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 150 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 150 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 150 179 (accept_3_2 1 150 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  179)))))))))))))))))))))))))))))) (allB_succ' 31 149 179 (Eq.refl Bool.true) (allA_succ_of_accept 30 149 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 149 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 149 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 179 (accept_3_2 28 149 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 149 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 149 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 179 (accept_3_2 25
  149 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 179
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 149 179 (Polychromatic418967fa.accept_20_3_9_19_1_4214 23 149 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 179 (accept_3_2 22 149 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 149 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 149 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 179 (Polychromatic418967fa.accept_7_6_2_4_1_291
  20 149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 179 (accept_3_2 19
  149 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 149 179 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 149 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 179 (accept_3_2 16 149 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 149 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 149 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 179 (accept_3_2 13
  149 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 149 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 149 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 179 (accept_3_2 10 149 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 149 179 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 149 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 179 (Polychromatic418967fa.accept_11_8_6_3_1_661 8
  149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 179 (accept_3_2 7 149
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 179 (Polychromatic418967fa.accept_4_2_1_3_1_27
  6 149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 179 (accept_3_2 4 149 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 149 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 179 (accept_3_2 1 149 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 179))))))))))))))))))))))))))))))) (allB_succ' 32 148 179 (Eq.refl Bool.true)
  (allA_of_3_0 32 148 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 147 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 147 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 179 (accept_3_2 31 147 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 179 (Polychromatic418967fa.accept_20_10_7_19_1_4293 30 147 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 179 (accept_3_2 28 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 179 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 147 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 179 (accept_3_2 25 147 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 147 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 179 (accept_3_2 22 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 179 (accept_3_2 19 147 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 179 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 147 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 179
  (Polychromatic418967fa.accept_14_3_7_11_1_765 17 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 179 (accept_3_2 16 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 147 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 179 (accept_3_2 13 147 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 179 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 147 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 179 (accept_3_2 10 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 179 (accept_3_2 7 147 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 147 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 179 (accept_3_2 4 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 179 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 147 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 147 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 179 (accept_3_2 1 147 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 179))))))))))))))))))))))))))))))))) (allB_succ' 34 146 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 146 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 146 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 146 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 146 179 (accept_3_2 31 146 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 146 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 30
  146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 146 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 146 179 (accept_3_2 28 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 146 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 146 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 146 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 146 179 (accept_3_2 25 146 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 146 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 146 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 146 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 146 179 (accept_3_2 22 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 146 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 146 179 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 146 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 146 179 (accept_3_2 19 146 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 146 179 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 146
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 146 179 (accept_3_2 16 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 146 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 146 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 146 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 179 (accept_3_2 13 146 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 146 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 179
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 146 179 (accept_3_2 10 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 146 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 179 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 146 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 179 (accept_3_2 7 146 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 146 179 (accept_3_2 4 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  146 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 146 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 146 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 146 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 179 (accept_3_2 1 146 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 146 179)))))))))))))))))))))))))))))))))) (allB_succ' 35 145 179 (Eq.refl Bool.true)
  (allA_of_3_0 35 145 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 144 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 179 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 144 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 179 (accept_3_2 34 144 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 144 179 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 144 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 179
  (Polychromatic418967fa.accept_23_9_6_18_1_10055 32 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 144 179 (accept_3_2 31 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 144 179 (Polychromatic418967fa.accept_13_4_1_10_1_693 30 144 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 179 (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 144
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 179 (accept_3_2 28 144
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 179
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 144 179 (Polychromatic418967fa.accept_19_7_11_8_1_8743 26 144 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 179 (accept_3_2 25 144 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 179 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 144
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 179
  (Polychromatic418967fa.accept_10_3_4_9_1_15 23 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 144 179 (accept_3_2 22 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 144 179 (Polychromatic418967fa.accept_14_7_4_11_1_3038 21 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 144 179 (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 144 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 179 (accept_3_2 19 144 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 144
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 179
  (Polychromatic418967fa.accept_13_4_1_10_1_693 17 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 144 179 (accept_3_2 16 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 144 179 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 144 179 (Polychromatic418967fa.accept_20_14_4_19_1_4288 14 144 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 179 (accept_3_2 13 144 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 179 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 144
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 179
  (Polychromatic418967fa.accept_13_11_1_10_1_648 11 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 179 (accept_3_2 10 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  144 179 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 144 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 144 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 179 (accept_3_2 7 144 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 179 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 144 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 179
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 179 (accept_3_2 4 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  144 179 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 144 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 144 179 (Polychromatic418967fa.accept_11_2_1_3_1_683 2 144 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 179 (accept_3_2 1 144 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 144 179)))))))))))))))))))))))))))))))))))) (allB_succ' 37 143 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 143 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 143 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 179 (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 143
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 179 (accept_3_2 34 143
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 179
  (Polychromatic418967fa.accept_23_10_5_18_1_6774 33 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 179 (Polychromatic418967fa.accept_17_15_7_9_1_1809 32 143 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 179 (accept_3_2 31 143 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 179 (Polychromatic418967fa.accept_19_11_10_8_1_7256 30 143
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 179 (accept_3_2 28 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 179 (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 143 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 179 (accept_3_2 25 143 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 143
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 179
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 23 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 179 (accept_3_2 22 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 179 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 143 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 179 (accept_3_2 19 143 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 179 (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 143 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 179
  (Polychromatic418967fa.accept_19_17_10_8_1_5942 17 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 143 179 (accept_3_2 16 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 143 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 143 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 143
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 179 (accept_3_2 13 143
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 179
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 143 179 (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 143 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 179 (accept_3_2 10 143 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 179 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 143 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 179 (accept_3_2 7 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 179 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 143 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 179 (accept_3_2 4 143 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 179 (Polychromatic418967fa.accept_24_3_23_11_1_8429 3 143 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 179
  (Polychromatic418967fa.accept_16_2_15_3_1_1300 2 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 179 (accept_3_2 1 143 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  179))))))))))))))))))))))))))))))))))))) (allB_succ' 38 142 179 (Eq.refl Bool.true) (allA_of_3_0 38 142 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 141 179 (Eq.refl Bool.true) (allA_succ_of_accept 38 141 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 179 (accept_3_2 37 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 141 179 (Polychromatic418967fa.accept_24_12_21_11_1_10131 36 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 141 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 179 (accept_3_2 34 141 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 141 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 179 (accept_3_2 31 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 141 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 141 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 141 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 179 (accept_3_2 28 141 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 141 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 179 (accept_3_2 25 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 141 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 179 (accept_3_2 22 141 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 179 (accept_3_2 19 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 141 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 179 (accept_3_2 16 141 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 141 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 179 (accept_3_2 13 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 141 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 179 (accept_3_2 10 141 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 179 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 141 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 179 (accept_3_2 7 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 141 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 179 (accept_3_2 4 141 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 141 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 179 (accept_3_2 1 141 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  179))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 140 179 (Eq.refl Bool.true) (allA_succ_of_accept 39 140 179
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 140 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 140 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 179 (accept_3_2 37 140 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 140 179 (Polychromatic418967fa.accept_15_6_5_14_1_429 36 140 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 140 179
  (Polychromatic418967fa.accept_19_16_7_8_1_8820 35 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 140 179 (accept_3_2 34 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 140 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 140 179 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 140 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 140 179 (accept_3_2 31 140 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 140 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 140 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 140 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 140 179 (accept_3_2 28 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 140 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 140 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 140 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 140 179 (accept_3_2 25 140 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 140 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 140 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 140 179
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 140 179 (accept_3_2 22 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 140 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 140 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 140 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 140 179 (accept_3_2 19 140 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 179 (Polychromatic418967fa.accept_19_18_7_8_1_2112 18 140 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 179
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 140 179 (accept_3_2 16 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 140 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 140 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 140 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 140 179 (accept_3_2 13 140 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 140 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 140 179 (accept_3_2 10 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  140 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 140 179 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 140 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 179 (accept_3_2 7 140 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 140 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 140 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 140 179
  (Polychromatic418967fa.accept_11_5_8_3_1_66 5 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 140 179 (accept_3_2 4 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  140 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 140 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 140 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 179 (accept_3_2 1 140 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 140 179)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 139 179 (Eq.refl
  Bool.true) (allA_of_3_0 41 139 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 138 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 138 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 179 (accept_3_2 40 138 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 138 179 (Polychromatic418967fa.accept_16_7_10_3_1_2210 39 138 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 138 179 (accept_3_2 37 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 138 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 138 179 (Polychromatic418967fa.accept_19_16_5_8_1_3253 35 138 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 179 (accept_3_2 34 138 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 138 179 (accept_3_2 31 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 138 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 138 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 138 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 179 (accept_3_2 28 138 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 138 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 179
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 179 (accept_3_2 25 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 138 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 138 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 138 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 179 (accept_3_2 22 138 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 138 179 (accept_3_2 19 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 138 179 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 138 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 179 (accept_3_2 16 138 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 138 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 179 (accept_3_2 13 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 138 179 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 138 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 179 (accept_3_2 10 138 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 179 (accept_3_2 7 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  138 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 138 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 179 (accept_3_2 4 138 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 179 (Polychromatic418967fa.accept_19_3_5_8_1_8790 3 138 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 179 (accept_3_2 1 138 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  179)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 137 179 (Eq.refl Bool.true) (allA_succ_of_accept 42 137
  179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 137 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 137 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 179 (accept_3_2 40 137 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 137 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 137 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 179 (accept_3_2 37
  137 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 179
  (Polychromatic418967fa.accept_19_17_4_8_1_4500 36 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 137 179 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 137 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 179 (accept_3_2 34 137 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 137 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 137 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 179 (Polychromatic418967fa.accept_9_5_2_8_1_109
  32 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 179 (accept_3_2 31
  137 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 137 179 (Polychromatic418967fa.accept_13_3_7_10_1_668 29 137 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 179 (accept_3_2 28 137 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 137 179 (Polychromatic418967fa.accept_15_12_2_14_1_5659 27 137 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 179 (accept_3_2 25 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 137 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 179 (accept_3_2 22 137 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 137 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 179
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 179 (accept_3_2 19 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 179 (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 137 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 179 (accept_3_2 16 137 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 137 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 179 (accept_3_2 13 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 179 (Polychromatic418967fa.accept_25_11_12_4_1_10130 11 137 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 179 (accept_3_2 10 137 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 179 (Polychromatic418967fa.accept_19_9_4_8_1_8805 9 137 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 179
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 179 (accept_3_2 7 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 137 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 179 (accept_3_2 4 137 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 137 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 179 (accept_3_2 1 137 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  179))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 136 179 (Eq.refl Bool.true) (allA_of_3_0 44 136 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 135 179 (Eq.refl Bool.true) (allA_succ_of_accept 44 135 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 179 (accept_3_2 43 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 135 179 (Polychromatic418967fa.accept_16_10_7_3_1_6601 42 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 135 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 135 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 179 (accept_3_2 40 135 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 179 (Polychromatic418967fa.accept_19_1_2_8_1_10129 39 135 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 179 (accept_3_2 37 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 135 179 (Polychromatic418967fa.accept_28_7_23_11_1_10128 35 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 179 (accept_3_2 34 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 135 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 179 (accept_3_2 31 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 179 (Polychromatic418967fa.accept_13_4_5_10_1_1247 30 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 179 (Polychromatic418967fa.accept_19_10_2_8_1_3206 29 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 179 (accept_3_2 28 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 135 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 179 (accept_3_2 25 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 179 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 179 (Polychromatic418967fa.accept_17_6_16_9_1_5129 23 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 179 (accept_3_2 22 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 179 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 135
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 179 (accept_3_2 19 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 179 (Polychromatic418967fa.accept_21_18_9_11_1_7082 18 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 179 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 179 (accept_3_2 16 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 179 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 135
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 179 (accept_3_2 13 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 179 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 179 (accept_3_2 10 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 135
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 179 (accept_3_2 7 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 135 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 179 (accept_3_2 4 135 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 179 (Polychromatic418967fa.accept_23_3_20_18_1_5037 3 135 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 179 (accept_3_2 1 135 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  179))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 134 179 (Eq.refl Bool.true) (allA_succ_of_accept 45
  134 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 134 179 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 134 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 134 179 (accept_3_2 43 134 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 134 179 (Polychromatic418967fa.accept_22_20_2_3_1_6916 42 134
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 134 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 134 179 (accept_3_2 40 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 134 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 134 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 134 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 134 179 (accept_3_2 37 134 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 134 179 (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 134 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 134 179
  (Polychromatic418967fa.accept_10_5_4_9_1_420 35 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 134 179 (accept_3_2 34 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 134 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 134 179 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 134 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 134 179 (accept_3_2 31 134 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 134 179 (Polychromatic418967fa.accept_19_11_1_8_1_10127 30 134
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 134 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 134 179 (accept_3_2 28 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 134 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 134 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 134 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 134 179 (accept_3_2 25 134 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 134 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 134 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 179
  (Polychromatic418967fa.accept_10_3_4_9_1_15 23 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 134 179 (accept_3_2 22 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 134 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 134 179 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 134 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 179 (accept_3_2 19 134 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 134
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 134 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 134 179 (accept_3_2 16 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 134 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 134 179 (Polychromatic418967fa.accept_13_1_4_10_1_622 14 134 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 179 (accept_3_2 13 134 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 134 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 179
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 134 179 (accept_3_2 10 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 134 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 134 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 179 (accept_3_2 7 134 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 179 (Polychromatic418967fa.accept_13_6_4_10_1_660
  6 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 134 179 (accept_3_2 4 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  134 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 134 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 134 179 (Polychromatic418967fa.accept_16_2_6_3_1_5396 2 134 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 179 (accept_3_2 1 134 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 134 179)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 133 179 (Eq.refl
  Bool.true) (allA_of_3_0 47 133 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 132 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 132 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 132 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 179 (accept_3_2 46 132 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 132 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 179 (accept_3_2 43
  132 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 179
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 132 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 132 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 179 (accept_3_2 40 132 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 132 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 179 (accept_3_2 37
  132 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 132 179
  (Polychromatic418967fa.accept_21_15_6_11_1_10126 36 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 179 (Polychromatic418967fa.accept_19_16_18_8_1_8784 35 132 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 179 (accept_3_2 34 132 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 132 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 132 179 (accept_3_2 31 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 132 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 132 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 179 (accept_3_2 28 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 179 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 132 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 179 (accept_3_2 25 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 179 (accept_3_2 22 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 132 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 179 (accept_3_2 19 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 132 179 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 179 (accept_3_2 16 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 132 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 179 (accept_3_2 13 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 132 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 132 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 179 (accept_3_2 10 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 132 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 179
  (Polychromatic418967fa.accept_13_8_2_10_1_652 8 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 179 (accept_3_2 7 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 179 (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 179 (accept_3_2 4 132 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 132 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 179 (accept_3_2 1 132 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  179)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 131 179 (Eq.refl Bool.true) (allA_succ_of_accept 48
  131 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 131 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 179 (accept_3_2 46 131 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 131 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 179 (accept_3_2 43 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 131 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 179 (accept_3_2 40 131 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 131 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 179 (accept_3_2 37 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 131 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 179 (accept_3_2 34 131 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 131 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 179
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 179 (accept_3_2 31 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 131 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 179 (accept_3_2 28 131 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 131 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 179
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 26 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 179 (accept_3_2 25 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 131 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 179 (accept_3_2 22 131 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 131 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 179 (accept_3_2 19 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 179 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 179 (Polychromatic418967fa.accept_13_4_1_10_1_693 17 131 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 179 (accept_3_2 16 131 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 131 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 179
  (Polychromatic418967fa.accept_17_14_12_9_1_2774 14 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 179 (accept_3_2 13 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 131 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 179 (accept_3_2 10 131 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 179 (accept_3_2 7 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 131 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 179 (accept_3_2 4 131 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 131 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 179 (accept_3_2 1 131 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  179))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 130 179 (Eq.refl Bool.true) (allA_of_3_0 50 130
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 129 179 (Eq.refl Bool.true) (allA_succ_of_accept 50 129
  179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 179 (accept_3_2 49 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 179 (accept_3_2 46 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 179 (Polychromatic418967fa.accept_13_6_12_10_1_690 45 129 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 179 (accept_3_2 43 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 179 (accept_3_2 40 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 179 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 129 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 179 (accept_3_2 37 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 179 (Polychromatic418967fa.accept_13_9_12_10_1_242 35 129 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 179 (accept_3_2 34 129 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 129 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 179 (accept_3_2 31 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 179 (accept_3_2 28 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 129 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 179 (accept_3_2 25 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 179 (accept_3_2 22 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 179 (Polychromatic418967fa.accept_13_8_12_10_1_4414 21 129 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 179 (accept_3_2 19 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 179 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 129 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 179 (accept_3_2 16 129 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 129 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 179 (accept_3_2 13 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 179 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 179 (accept_3_2 10 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 179 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 129 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 179 (accept_3_2 7 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 179 (accept_3_2 4 129 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 129 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 179 (accept_3_2 1 129 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  179))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 128 179 (Eq.refl Bool.true) (allA_succ_of_accept
  51 128 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 128 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 128 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 128 179 (accept_3_2 49 128 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 128 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 128 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 128 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 128 179 (accept_3_2 46 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 128 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 128 179 (Polychromatic418967fa.accept_10_4_8_9_1_784 44 128 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 179 (accept_3_2 43 128 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 128 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 128 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 179
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 128 179 (accept_3_2 40 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 128 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 128 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 128 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 179 (accept_3_2 37 128 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 128 179 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 128
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 179
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 179 (accept_3_2 34 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 128 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 179 (accept_3_2 31 128 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 128 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 179
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 29 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 128 179 (accept_3_2 28 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 128 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 128 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 128 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 179 (accept_3_2 25 128 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 179 (Polychromatic418967fa.accept_9_6_2_8_1_592
  24 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 128 179 (accept_3_2 22 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 128 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 128 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 128 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 179 (accept_3_2 19 128 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 179 (Polychromatic418967fa.accept_24_18_8_11_1_10125 18 128 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 179
  (Polychromatic418967fa.accept_10_7_8_9_1_785 17 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 128 179 (accept_3_2 16 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 128 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 128 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 128 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 179 (accept_3_2 13 128 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 128 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 179
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 128 179 (accept_3_2 10 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  128 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 128 179 (Polychromatic418967fa.accept_13_8_11_10_1_636 8 128 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 179 (accept_3_2 7 128 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 128 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 179 (accept_3_2 4 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 128 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 179 (accept_3_2 1 128 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128 179)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 127 179
  (Eq.refl Bool.true) (allA_of_3_0 53 127 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 126 179 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 126 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 179 (accept_3_2 52 126 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 179 (Polychromatic418967fa.accept_13_12_9_10_1_1223 51 126 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 179
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 50 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 126 179 (accept_3_2 49 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 126 179 (Polychromatic418967fa.accept_19_10_12_8_1_10124 48 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 179 (Polychromatic418967fa.accept_20_7_6_19_1_2949 47 126 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 179 (accept_3_2 46 126 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 126 179
  (Polychromatic418967fa.accept_19_6_12_8_1_8798 44 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 126 179 (accept_3_2 43 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 126 179 (Polychromatic418967fa.accept_19_4_12_8_1_10123 42 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 126 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 179 (accept_3_2 40 126 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 179 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 126 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 179
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 38 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 126 179 (accept_3_2 37 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 126 179 (Polychromatic418967fa.accept_17_2_7_9_1_2796 36 126 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 179 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 126
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 179 (accept_3_2 34 126
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 179 (Polychromatic418967fa.accept_4_1_2_3_1_9
  33 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 179
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 32 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 179 (accept_3_2 31 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 126 179 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 126 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 126 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 179 (accept_3_2 28 126 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 179 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 126 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 179
  (Polychromatic418967fa.accept_19_7_12_8_1_10122 26 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 126 179 (accept_3_2 25 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 126 179 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 126 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 126
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 179 (accept_3_2 22 126
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 179 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 179
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 179 (accept_3_2 19 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 126 179 (Polychromatic418967fa.accept_24_18_6_11_1_10090 18 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 179 (accept_3_2 16 126 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 179 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 126
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 179
  (Polychromatic418967fa.accept_13_1_9_10_1_625 14 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 179 (accept_3_2 13 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 126 179 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 179 (Polychromatic418967fa.accept_16_11_14_3_1_3140 11 126 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 179 (accept_3_2 10 126 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 179
  (Polychromatic418967fa.accept_11_8_5_3_1_694 8 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 126 179 (accept_3_2 7 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  126 179 (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 126 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 179 (accept_3_2 4 126 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 126 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 179
  (Polychromatic418967fa.accept_17_2_7_9_1_2796 2 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 179 (accept_3_2 1 126 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 125 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 125 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 125 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 179 (Polychromatic418967fa.accept_15_8_5_14_1_986 53 125
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 179 (accept_3_2 52 125
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 125 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 125 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 179 (accept_3_2 49 125 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 125 179 (Polychromatic418967fa.accept_19_10_11_8_1_10121 48 125 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 179 (accept_3_2 46 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 125 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 179 (accept_3_2 43 125 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 179
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 179 (accept_3_2 40 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 179 (Polychromatic418967fa.accept_15_9_5_14_1_973 39 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 179 (accept_3_2 37 125 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 179 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 125 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 179
  (Polychromatic418967fa.accept_19_16_11_8_1_8758 35 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 125 179 (accept_3_2 34 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 125 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 125 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 179 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 125
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 179 (accept_3_2 31 125
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 125 179 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 125 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 179 (accept_3_2 28 125 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 125 179 (Polychromatic418967fa.accept_21_6_20_11_1_7067 27 125 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 179 (accept_3_2 25 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 125 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 179 (accept_3_2 22 125 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 179 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 125 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 179
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 179 (accept_3_2 19 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 125 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 179 (accept_3_2 16 125 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 179 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 125 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 179 (accept_3_2 13 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 179 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 125 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 179 (accept_3_2 10 125 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 125 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 179
  (Polychromatic418967fa.accept_15_8_5_14_1_986 8 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 179 (accept_3_2 7 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 125 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 179 (accept_3_2 4 125 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 125 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 179 (accept_3_2 1 125 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  179))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 124 179 (Eq.refl Bool.true) (allA_of_3_0 56
  124 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 123 179 (Eq.refl Bool.true) (allA_succ_of_accept 56
  123 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 123 179 (accept_3_2 55 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 123 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 123 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 179 (Polychromatic418967fa.accept_17_2_4_9_1_2791 53 123
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 179 (accept_3_2 52 123
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 123 179
  (Polychromatic418967fa.accept_13_12_6_10_1_667 51 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 123 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 123 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 179 (accept_3_2 49 123 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 123 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 179 (Polychromatic418967fa.accept_9_2_6_8_1_321
  47 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 179 (accept_3_2 46
  123 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 179
  (Polychromatic418967fa.accept_11_1_2_3_1_688 45 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 123 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 123 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 179 (accept_3_2 43 123 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 123 179 (Polychromatic418967fa.accept_13_3_6_10_1_2658 42 123 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 179 (accept_3_2 40 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 179 (accept_3_2 37 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 179 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 123 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 179
  (Polychromatic418967fa.accept_13_9_6_10_1_666 35 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 179 (accept_3_2 34 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 179 (accept_3_2 31 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 123 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 179 (accept_3_2 28 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 179 (Polychromatic418967fa.accept_18_9_15_17_1_3497 27 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 179 (accept_3_2 25 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 123 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 179 (accept_3_2 22 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 179 (accept_3_2 19 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 179 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 123 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 179
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 179 (accept_3_2 16 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 179 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 179 (accept_3_2 13 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 123 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 179 (accept_3_2 10 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 179 (accept_3_2 7 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 179 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 123 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 179 (accept_3_2 4 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 123 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 179 (accept_3_2 1 123 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 122 179
  (Eq.refl Bool.true) (allA_succ_of_accept 57 122 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 122 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 122 179 (accept_3_2 55 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 179 (Polychromatic418967fa.accept_13_2_5_10_1_250 54 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 179 (accept_3_2 52 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 122 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 179 (accept_3_2 49 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 179 (accept_3_2 46 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 179 (accept_3_2 43 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 179 (accept_3_2 40 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 122 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 179 (accept_3_2 37 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 122 179 (Polychromatic418967fa.accept_11_2_1_3_1_683 35 122 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 179 (accept_3_2 34 122 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 179 (accept_3_2 31 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 179 (accept_3_2 28 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 122 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 179
  (Polychromatic418967fa.accept_21_5_17_11_1_7021 26 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 122 179 (accept_3_2 25 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 122 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 122 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 179 (Polychromatic418967fa.accept_16_7_10_3_1_2210 23 122
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 179 (accept_3_2 22 122
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 179 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 179
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 179 (accept_3_2 19 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 179 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 179 (accept_3_2 16 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 122 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 179
  (Polychromatic418967fa.accept_22_14_12_3_1_10089 14 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 122 179 (accept_3_2 13 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 122 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 122 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 122 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 179 (accept_3_2 10 122 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 179 (accept_3_2 7 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 179 (accept_3_2 4 122 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 122 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 179 (accept_3_2 1 122 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 121 179 (Eq.refl Bool.true) (allA_of_3_0
  59 121 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 120 179 (Eq.refl Bool.true) (allA_succ_of_accept 59
  120 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 120 179 (accept_3_2 58 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 120 179 (Polychromatic418967fa.accept_22_13_10_3_1_8613 57 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 179 (Polychromatic418967fa.accept_9_2_3_8_1_318
  56 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 120 179 (accept_3_2 55
  120 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 120 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 120 179 (Polychromatic418967fa.accept_16_5_8_3_1_4240 53 120 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 179 (accept_3_2 52 120 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 120 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 179 (Polychromatic418967fa.accept_9_5_3_8_1_316
  50 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 179 (accept_3_2 49
  120 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 179
  (Polychromatic418967fa.accept_21_6_15_11_1_5410 48 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 120 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 179 (accept_3_2 46 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 120 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 179
  (Polychromatic418967fa.accept_16_12_8_3_1_4241 44 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 179 (accept_3_2 43 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 120 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 120 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 179 (accept_3_2 40 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 179 (Polychromatic418967fa.accept_22_17_10_3_1_10120 39 120 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 179 (accept_3_2 37 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 120 179 (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 120 179 (Polychromatic418967fa.accept_19_16_6_8_1_8772 35 120 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 179 (accept_3_2 34 120 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 120 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 179 (accept_3_2 31 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 120 179 (Polychromatic418967fa.accept_21_9_15_11_1_7018 30 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 179 (accept_3_2 28 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 179 (Polychromatic418967fa.accept_16_11_8_3_1_3183 27 120 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 120 179 (accept_3_2 25 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 120 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 179 (accept_3_2 22 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 179 (Polychromatic418967fa.accept_16_5_8_3_1_4240 21 120 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 179 (accept_3_2 19 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 179 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 179 (accept_3_2 16 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 120 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 179 (accept_3_2 13 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 120 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 120 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 179 (accept_3_2 10 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 179 (Polychromatic418967fa.accept_18_9_12_17_1_6060 9 120 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 179
  (Polychromatic418967fa.accept_17_8_1_9_1_7738 8 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 179 (accept_3_2 7 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 120 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 179 (accept_3_2 4 120 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 179 (accept_3_2 1 120 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 119 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 119 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 119 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 119 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 179 (accept_3_2 58 119 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 179 (Polychromatic418967fa.accept_9_3_2_8_1_108
  57 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 179
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 56 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 119 179 (accept_3_2 55 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 119 179 (Polychromatic418967fa.accept_19_16_5_8_1_3253 54 119 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 179 (Polychromatic418967fa.accept_24_5_23_11_1_10119 53
  119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 179 (accept_3_2 52
  119 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 179
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 119 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 119 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 179 (accept_3_2 49 119 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 119 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 119 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 179 (Polychromatic418967fa.accept_13_8_2_10_1_652
  47 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 179 (accept_3_2 46
  119 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 179
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 119 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 119 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 179 (accept_3_2 43 119 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 119 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 119 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 179 (Polychromatic418967fa.accept_9_5_2_8_1_109
  41 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 179 (accept_3_2 40
  119 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 119 179 (Polychromatic418967fa.accept_13_12_2_10_1_2698 38 119 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 179 (accept_3_2 37 119 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 119 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 179
  (Polychromatic418967fa.accept_19_16_5_8_1_3253 35 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 179 (accept_3_2 34 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 179 (accept_3_2 31 119 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 119 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 179
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 29 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 179 (accept_3_2 28 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 179 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 179 (Polychromatic418967fa.accept_16_10_7_3_1_6601 26 119 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 179 (accept_3_2 25 119 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 179 (accept_3_2 22 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 119 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 179 (accept_3_2 19 119 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 179 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 119 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 179
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 179 (accept_3_2 16 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 119 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 179 (accept_3_2 13 119 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 119 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 179
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 119 179 (accept_3_2 10 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 119 179 (Polychromatic418967fa.accept_16_9_7_3_1_614 9 119 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 179 (Polychromatic418967fa.accept_13_8_2_10_1_652 8 119 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 179 (accept_3_2 7 119 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 179 (accept_3_2 4 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 119 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 179 (Polychromatic418967fa.accept_18_2_11_17_1_4773 2 119 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 179 (accept_3_2 1 119 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 119 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 118 179 (Eq.refl Bool.true) (allA_of_3_0 62 118 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 63 117 179 (Eq.refl Bool.true) (allA_succ_of_accept 62 117 179 (Polychromatic418967fa.accept_4_2_1_3_1_27
  62 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 179 (accept_3_2 61
  117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 179
  (Polychromatic418967fa.accept_21_18_12_11_1_7078 60 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 117 179 (Polychromatic418967fa.accept_11_4_7_3_1_289 59 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 179 (accept_3_2 58 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 117 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 179 (accept_3_2 55 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 179 (Polychromatic418967fa.accept_19_15_3_8_1_8789 53 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 179 (accept_3_2 52 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 117 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 179 (accept_3_2 49 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 117 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 179 (Polychromatic418967fa.accept_15_2_12_14_1_1709 47 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 179 (accept_3_2 46 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 179 (Polychromatic418967fa.accept_21_3_12_11_1_7034 45 117
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 179 (accept_3_2 43 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 117 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 117 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 179 (accept_3_2 40 117 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 179 (accept_3_2 37 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 179 (Polychromatic418967fa.accept_17_1_15_9_1_1743 35 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 179 (accept_3_2 34 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 179 (Polychromatic418967fa.accept_18_15_9_17_1_6043 33 117
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 179 (accept_3_2 31 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 117 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 179 (accept_3_2 28 117 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 179 (accept_3_2 25 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 179 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 117 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 179 (accept_3_2 22 117 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 179 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 117 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 179 (accept_3_2 19 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 179 (Polychromatic418967fa.accept_15_2_12_14_1_1709 17 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 179 (accept_3_2 16 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 117 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 179 (accept_3_2 13 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 179 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 179 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 179 (accept_3_2 10 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 179 (accept_3_2 7 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 179 (Polychromatic418967fa.accept_19_5_3_8_1_7302 5 117 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 179 (accept_3_2 4 117 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 117 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 179 (accept_3_2 1 117 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 116 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 116 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 62 116
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 116 179 (accept_3_2 61 116
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 179
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 116 179 (Polychromatic418967fa.accept_13_7_12_10_1_640 59 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 116 179 (accept_3_2 58 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 116 179
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 56 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 116 179 (accept_3_2 55 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 116 179 (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 116 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 116 179 (accept_3_2 52 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 116 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 116 179 (accept_3_2 49 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 116 179 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 116 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 116 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 116 179 (accept_3_2 46 116 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 179
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 44 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 116 179 (accept_3_2 43 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 116 179 (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 116 179 (Polychromatic418967fa.accept_11_8_6_3_1_661 41 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 179 (accept_3_2 40 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 116 179 (accept_3_2 37 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 116 179 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 116 179 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 179 (accept_3_2 34 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 179
  (Polychromatic418967fa.accept_13_6_12_10_1_690 32 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 179 (accept_3_2 31 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 179 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 179 (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 179 (accept_3_2 28 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 116 179 (accept_3_2 25 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 116 179 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 179 (accept_3_2 22 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 179
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 179 (accept_3_2 19 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 179 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 179 (Polychromatic418967fa.accept_16_1_4_3_1_3148 17 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 179 (accept_3_2 16 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 179 (accept_3_2 13 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 179 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 179 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 116 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 179 (accept_3_2 10 116 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9
  116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 179
  (Polychromatic418967fa.accept_11_8_6_3_1_661 8 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 179 (accept_3_2 7 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 179 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 179 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 116 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 179 (accept_3_2 4 116 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 179 (accept_3_2 1 116 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 115 179 (Eq.refl Bool.true)
  (allA_of_3_0 65 115 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 114 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 114 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 114 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 179 (accept_3_2 64 114 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 114 179 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 179 (Polychromatic418967fa.accept_7_6_2_4_1_291
  62 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 179 (accept_3_2 61
  114 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 179
  (Polychromatic418967fa.accept_21_18_9_11_1_7082 60 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 114 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 179 (accept_3_2 58 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 179 (accept_3_2 55 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 114 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 114 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 179 (accept_3_2 52 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 179 (Polychromatic418967fa.accept_11_7_4_3_1_302 51 114 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 114 179 (accept_3_2 49 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 114 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 114 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 179 (accept_3_2 46 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 179
  (Polychromatic418967fa.accept_20_4_14_19_1_4222 44 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 114 179 (accept_3_2 43 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 114 179 (Polychromatic418967fa.accept_15_12_9_14_1_2635 42 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 114 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 179 (accept_3_2 40
  114 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 179
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 114 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 114 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 179 (accept_3_2 37 114 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 114 179 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 114 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 114 179
  (Polychromatic418967fa.accept_10_5_4_9_1_420 35 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 179 (accept_3_2 34 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 114 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 114 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 179 (accept_3_2 31 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 114 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 114 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 114 179 (accept_3_2 28 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 114 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 114 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 179 (accept_3_2 25 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 179 (Polychromatic418967fa.accept_20_4_14_19_1_4222 24 114 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 179 (accept_3_2 22 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 114 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 114 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 179 (accept_3_2 19 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 114 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 179 (accept_3_2 16 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 114 179 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 114 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 179 (accept_3_2 13 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 114 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 179 (accept_3_2 10 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 179 (accept_3_2 7 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 114 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 179 (accept_3_2 4 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 114 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 179 (accept_3_2 1 114 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  67 113 179 (Eq.refl Bool.true) (allA_succ_of_accept 66 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 179 (accept_3_2 64 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 179 (Polychromatic418967fa.accept_26_11_9_23_1_10118 63 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 179 (accept_3_2 61 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 113 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 179 (accept_3_2 58 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 113 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 179 (accept_3_2 55 113 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 179
  (Polychromatic418967fa.accept_13_1_9_10_1_625 53 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 179 (accept_3_2 52 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 179 (accept_3_2 49 113 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 179 (accept_3_2 46 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 179 (accept_3_2 43 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 179
  (Polychromatic418967fa.accept_21_20_8_11_1_5407 41 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 113 179 (accept_3_2 40 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 113 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 113 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 179 (accept_3_2 37 113 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 179 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  36 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 179
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 179 (accept_3_2 34 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 179 (Polychromatic418967fa.accept_13_6_9_10_1_1201 32 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 179 (accept_3_2 31 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 179 (accept_3_2 28 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 179 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 179 (accept_3_2 25 113 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 179
  (Polychromatic418967fa.accept_19_4_18_8_1_10117 23 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 113 179 (accept_3_2 22 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 113 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 113 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 113 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 179 (accept_3_2 19 113 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 179 (accept_3_2 16 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 179 (accept_3_2 13 113 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 179 (accept_3_2 10 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 179 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 179 (Polychromatic418967fa.accept_17_8_11_9_1_5099 8 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 179 (accept_3_2 7 113 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 179 (accept_3_2 4 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 113 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 179 (accept_3_2 1 113 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 112 179 (Eq.refl Bool.true) (allA_of_3_0 68 112 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 111 179
  (Eq.refl Bool.true) (allA_succ_of_accept 68 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 179 (accept_3_2 67 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 111 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 179 (accept_3_2 64 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 179 (Polychromatic418967fa.accept_19_6_16_8_1_10116 63 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 179 (accept_3_2 61 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 179
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 179 (accept_3_2 58 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 179 (Polychromatic418967fa.accept_11_2_1_3_1_683 57 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 179 (accept_3_2 55 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 179
  (Polychromatic418967fa.accept_15_8_6_14_1_975 53 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 179 (accept_3_2 52 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 179 (accept_3_2 49 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 179 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 179 (accept_3_2 46 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 179 (accept_3_2 43 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 179 (accept_3_2 40 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 179 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 179 (accept_3_2 37 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 179
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 179 (accept_3_2 34 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 179 (accept_3_2 31 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 179 (accept_3_2 28 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 179 (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 179 (accept_3_2 25 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 179 (accept_3_2 22 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 179 (accept_3_2 19 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 179 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 179
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 179 (accept_3_2 16 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 179 (accept_3_2 13 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 179 (accept_3_2 10 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 179 (accept_3_2 7 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 179 (accept_3_2 4 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 179 (accept_3_2 1 111 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 110 179 (Eq.refl Bool.true) (allA_succ_of_accept 69 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9
  69 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 110 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 110 179 (accept_3_2 67 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 110 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 110 179 (accept_3_2 64 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 110 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 110 179 (accept_3_2 61 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 110 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 110 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 110 179 (accept_3_2 58 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 110 179 (accept_3_2 55 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 110 179 (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 179 (accept_3_2 52 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 110 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 110 179 (accept_3_2 49 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 110 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 110 179 (Polychromatic418967fa.accept_15_2_5_14_1_61 47 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 179 (accept_3_2 46 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 110 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 110 179 (accept_3_2 43 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 110 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 179 (accept_3_2 40 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 110 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 179
  (Polychromatic418967fa.accept_13_12_6_10_1_667 38 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 110 179 (accept_3_2 37 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 110 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 110 179 (Polychromatic418967fa.accept_13_9_6_10_1_666 35 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 179 (accept_3_2 34 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 110 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 179 (accept_3_2 31 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 179 (accept_3_2 28 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 179
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 110 179 (accept_3_2 25 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 110 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 110 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 179 (accept_3_2 22 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 110 179 (accept_3_2 19 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 110 179 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 179 (accept_3_2 16 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 179 (accept_3_2 13 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 179 (Polychromatic418967fa.accept_16_11_14_3_1_3140 11 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 179 (accept_3_2 10 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 179 (accept_3_2 7 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 179 (accept_3_2 4 110 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 110 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 179 (accept_3_2 1 110 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 109 179 (Eq.refl Bool.true)
  (allA_of_3_0 71 109 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 108 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 108 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 108 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 179 (accept_3_2 70 108 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 108 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 179
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 68 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 179 (accept_3_2 67 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 108 179 (Polychromatic418967fa.accept_13_1_4_10_1_622 66 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 179 (Polychromatic418967fa.accept_25_15_8_4_1_10115 65 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 179 (accept_3_2 64 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 108 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 179
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 179 (accept_3_2 61 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 108 179 (Polychromatic418967fa.accept_13_8_4_10_1_4358 60 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 108 179 (Polychromatic418967fa.accept_13_7_4_10_1_2675 59 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 179 (accept_3_2 58 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 108 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 179
  (Polychromatic418967fa.accept_15_11_3_14_1_971 56 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 108 179 (accept_3_2 55 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 108 179 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 108 179 (Polychromatic418967fa.accept_13_1_4_10_1_622 53 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 179 (accept_3_2 52 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 179 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 108
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 108 179 (accept_3_2 49 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 108 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 108 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 179 (accept_3_2 46 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 179 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 179
  (Polychromatic418967fa.accept_10_4_8_9_1_784 44 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 108 179 (accept_3_2 43 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 108 179 (Polychromatic418967fa.accept_16_10_12_3_1_4252 42 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 108 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 179 (accept_3_2 40 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 179
  (Polychromatic418967fa.accept_22_16_20_3_1_10114 38 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 108 179 (accept_3_2 37 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 108 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 108 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 179 (Polychromatic418967fa.accept_14_7_10_11_1_8112 35 108
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 179 (accept_3_2 34 108
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 179
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 33 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 179 (Polychromatic418967fa.accept_13_6_4_10_1_660 32 108 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 179 (accept_3_2 31 108 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 108 179 (Polychromatic418967fa.accept_22_8_20_3_1_10063 30 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 179 (accept_3_2 28 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 108 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 108 179 (Polychromatic418967fa.accept_15_11_3_14_1_971 26 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 179 (accept_3_2 25 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 179 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 108
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 179
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 179 (accept_3_2 22 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 108 179 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 108 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 179 (accept_3_2 19 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 179 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 108 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 179
  (Polychromatic418967fa.accept_10_7_8_9_1_785 17 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 179 (accept_3_2 16 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 108 179 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 179 (accept_3_2 13 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 179 (Polychromatic418967fa.accept_21_12_3_11_1_10078 12
  108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 179
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 179 (accept_3_2 10 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 179 (Polychromatic418967fa.accept_16_9_12_3_1_3138 9 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 179 (accept_3_2 7 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 108 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 179
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 179 (accept_3_2 4 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 179 (Polychromatic418967fa.accept_17_3_6_9_1_2761 3 108 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 179 (Polychromatic418967fa.accept_15_2_3_14_1_972 2 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 179 (accept_3_2 1 108 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 73 107 179 (Eq.refl Bool.true) (allA_succ_of_accept 72 107 179
  (Polychromatic418967fa.accept_10_2_7_9_1_783 72 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 107 179 (Polychromatic418967fa.accept_11_5_8_3_1_66 71 107 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 179 (accept_3_2 70 107 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 107 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 107 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 179 (Polychromatic418967fa.accept_7_5_2_4_1_126
  68 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 179 (accept_3_2 67
  107 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 179
  (Polychromatic418967fa.accept_20_6_7_19_1_7185 66 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 107 179 (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 107 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 179 (accept_3_2 64 107 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 107 179 (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 179
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 179 (accept_3_2 61 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 179 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 179 (Polychromatic418967fa.accept_13_7_3_10_1_656 59 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 179 (accept_3_2 58 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 179 (Polychromatic418967fa.accept_15_12_2_14_1_5659 57 107
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 179
  (Polychromatic418967fa.accept_16_8_11_3_1_4279 56 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 179 (accept_3_2 55 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 179 (Polychromatic418967fa.accept_19_15_12_8_1_5922 53 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 179 (accept_3_2 52 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 179 (Polychromatic418967fa.accept_21_9_2_11_1_10112 51 107
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 179
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 50 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 179 (accept_3_2 49 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 107 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 179 (accept_3_2 46 107 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 179 (Polychromatic418967fa.accept_13_6_3_10_1_698 45 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 179
  (Polychromatic418967fa.accept_14_2_9_11_1_3054 44 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 179 (accept_3_2 43 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 179 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 107 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 179 (accept_3_2 40 107 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 179 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 179
  (Polychromatic418967fa.accept_10_8_7_9_1_425 38 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 179 (accept_3_2 37 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 179 (Polychromatic418967fa.accept_25_11_7_4_1_10113 36 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 179 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 179 (accept_3_2 34 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 107 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 179
  (Polychromatic418967fa.accept_10_2_7_9_1_783 32 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 179 (accept_3_2 31 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 179 (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 179 (Polychromatic418967fa.accept_17_12_5_9_1_6372 29 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 179 (accept_3_2 28 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 107 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 179 (accept_3_2 25 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 179 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 179 (Polychromatic418967fa.accept_16_7_11_3_1_1330 23 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 179 (accept_3_2 22 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 179 (Polychromatic418967fa.accept_23_21_15_18_1_5047 21
  107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 179
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 179 (accept_3_2 19 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 179 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 179 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 179 (accept_3_2 16 107 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 179 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 107
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 179
  (Polychromatic418967fa.accept_16_14_11_3_1_4249 14 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 107 179 (accept_3_2 13 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 107 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 107 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 179 (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 107
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 179 (accept_3_2 10 107
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 179
  (Polychromatic418967fa.accept_21_9_2_11_1_10112 9 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 107 179 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 107 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 179 (accept_3_2 7 107 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 107 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 107 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 5
  107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 179 (accept_3_2 4 107
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 179
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 107 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 107 179 (Polychromatic418967fa.accept_10_2_7_9_1_783 2 107 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 179 (accept_3_2 1 107 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 107 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  106 179 (Eq.refl Bool.true) (allA_of_3_0 74 106 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 105 179
  (Eq.refl Bool.true) (allA_succ_of_accept 74 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 179 (accept_3_2 73 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 179 (Polychromatic418967fa.accept_25_22_5_4_1_10111 72 105
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 179
  (Polychromatic418967fa.accept_10_1_5_9_1_157 71 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 179 (accept_3_2 70 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 179 (Polychromatic418967fa.accept_13_4_1_10_1_693 69 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 179 (accept_3_2 67 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 179 (accept_3_2 64 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 179 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 179 (accept_3_2 61 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 179 (Polychromatic418967fa.accept_14_4_7_11_1_790 60 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 179 (accept_3_2 58 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 179 (accept_3_2 55 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 179
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 53 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 179 (accept_3_2 52 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 179 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 179 (accept_3_2 49 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 179 (accept_3_2 46 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 179 (Polychromatic418967fa.accept_14_3_7_11_1_765 45 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 179 (accept_3_2 43 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 179 (accept_3_2 40 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 179 (accept_3_2 37 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 179 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 179
  (Polychromatic418967fa.accept_13_9_1_10_1_647 35 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 179 (accept_3_2 34 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 179 (Polychromatic418967fa.accept_20_13_5_19_1_10110 33 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 179 (accept_3_2 31 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 179 (accept_3_2 28 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 179 (accept_3_2 25 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 179 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 179 (accept_3_2 22 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 179 (accept_3_2 19 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 179
  (Polychromatic418967fa.accept_13_4_1_10_1_693 17 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 179 (accept_3_2 16 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 179 (accept_3_2 13 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 179 (accept_3_2 10 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 179 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 179 (accept_3_2 7 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 179 (accept_3_2 4 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 179 (accept_3_2 1 105 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 76 104 179 (Eq.refl Bool.true) (allA_succ_of_accept 75 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32
  75 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 104 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 104 179 (accept_3_2 73 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 104 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 104 179 (Polychromatic418967fa.accept_19_14_9_8_1_7271 71 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 104 179 (accept_3_2 70 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 104 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 104 179 (accept_3_2 67 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 104 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 104 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 104 179 (accept_3_2 64 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 104 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 104 179 (accept_3_2 61 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 104 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 104 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 104 179 (accept_3_2 58 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 104 179 (accept_3_2 55 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 104 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 104 179 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 179 (accept_3_2 52 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 104 179 (accept_3_2 49 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 104 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 104 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 179 (accept_3_2 46 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 104 179 (accept_3_2 43 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 104 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 104 179 (Polychromatic418967fa.accept_11_8_5_3_1_694 41 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 179 (accept_3_2 40 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 179
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 179 (accept_3_2 37 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 179 (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 179 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 179 (accept_3_2 34 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 179
  (Polychromatic418967fa.accept_22_10_16_3_1_10109 32 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 104 179 (accept_3_2 31 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 104 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 104 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 104 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 179 (accept_3_2 28 104 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 179 (accept_3_2 25 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 179 (accept_3_2 22 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 179 (accept_3_2 19 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 179 (accept_3_2 16 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 179 (accept_3_2 13 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 179 (accept_3_2 10 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 179
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 179 (accept_3_2 7 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 179 (accept_3_2 4 104 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 179 (accept_3_2 1 104 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 103 179 (Eq.refl
  Bool.true) (allA_of_3_0 77 103 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 102 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 102 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 179 (accept_3_2 76 102 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 102 179 (Polychromatic418967fa.accept_16_11_6_3_1_6564 75 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 102 179 (accept_3_2 73 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 102 179 (Polychromatic418967fa.accept_19_15_7_8_1_8755 72 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 102 179 (Polychromatic418967fa.accept_10_1_2_9_1_152 71 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 179 (accept_3_2 70 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 102 179 (accept_3_2 67 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 102 179 (Polychromatic418967fa.accept_13_1_11_10_1_1258 66 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 179 (accept_3_2 64 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 179 (Polychromatic418967fa.accept_14_7_4_11_1_3038 63 102 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 179
  (Polychromatic418967fa.accept_15_2_12_14_1_1709 62 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 102 179 (accept_3_2 61 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 102 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 102 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 102 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 102 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 179 (accept_3_2 58 102 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 102 179 (accept_3_2 55 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 102 179 (Polychromatic418967fa.accept_13_2_11_10_1_1881 54 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 179 (accept_3_2 52 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 179 (accept_3_2 49 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 102 179 (Polychromatic418967fa.accept_21_6_18_11_1_3960 48 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 179 (accept_3_2 46 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 179
  (Polychromatic418967fa.accept_19_6_7_8_1_10108 44 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 179 (accept_3_2 43 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 179 (accept_3_2 40 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 179 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 102 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 179 (accept_3_2 37 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 179 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 179 (Polychromatic418967fa.accept_14_7_4_11_1_3038 35 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 179 (accept_3_2 34 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 179 (accept_3_2 31 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 102 179 (Polychromatic418967fa.accept_13_4_11_10_1_1226 30 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 179 (accept_3_2 28 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 179 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 179
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 102 179 (accept_3_2 25 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 102 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 102 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 102 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 179 (accept_3_2 22 102 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 179 (accept_3_2 19 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 102 179 (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 179 (accept_3_2 16 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 179 (accept_3_2 13 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 179 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 179 (accept_3_2 10 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 179
  (Polychromatic418967fa.accept_13_8_11_10_1_636 8 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 179 (accept_3_2 7 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 179 (accept_3_2 4 102 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 179 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 102 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 179 (accept_3_2 1 102 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 101 179 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 101 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 179 (Polychromatic418967fa.accept_9_5_2_8_1_109
  77 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 179 (accept_3_2 76
  101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 101 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 179 (accept_3_2 73 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 101 179 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 101 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 179 (accept_3_2 70 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 179 (accept_3_2 67 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 179
  (Polychromatic418967fa.accept_10_5_1_9_1_791 65 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 179 (accept_3_2 64 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 179 (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 179 (accept_3_2 61 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 101 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 179 (accept_3_2 58 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 179 (Polychromatic418967fa.accept_11_1_2_3_1_688 56 101 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 179 (accept_3_2 55 101 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 179
  (Polychromatic418967fa.accept_25_3_1_4_1_10107 53 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 179 (accept_3_2 52 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 179 (accept_3_2 49 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 101 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 179
  (Polychromatic418967fa.accept_17_13_16_9_1_5128 47 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 101 179 (accept_3_2 46 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 101 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 179 (Polychromatic418967fa.accept_17_10_16_9_1_5127 44 101
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 179 (accept_3_2 43 101
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 101 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 179 (accept_3_2 40 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 101 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 179 (accept_3_2 37
  101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 101 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 179 (accept_3_2 34 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 101 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 179 (Polychromatic418967fa.accept_9_5_2_8_1_109
  32 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 179 (accept_3_2 31
  101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 101 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 179 (accept_3_2 28 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 101 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 179 (accept_3_2 25
  101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 179
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 101 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 179 (accept_3_2 22 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 101 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 179 (Polychromatic418967fa.accept_7_6_3_4_1_294
  20 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 179 (accept_3_2 19
  101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 101 179 (Polychromatic418967fa.accept_19_17_6_8_1_5928 17 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 179 (accept_3_2 16 101 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 101 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 179 (accept_3_2 13
  101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 101 179 (Polychromatic418967fa.accept_22_11_13_3_1_10106 11 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 179 (accept_3_2 10 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 179 (Polychromatic418967fa.accept_27_9_20_17_1_10105 9 101 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 179 (accept_3_2 7 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 179 (accept_3_2 4 101 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 101 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 179 (accept_3_2 1 101 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 100 179 (Eq.refl
  Bool.true) (allA_of_3_0 80 100 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 99 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 80 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 179 (accept_3_2 79 99 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 179 (Polychromatic418967fa.accept_22_12_11_3_1_10104 78 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 179
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 77 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 99 179 (accept_3_2 76 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  99 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 179 (accept_3_2 73 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 99 179 (Polychromatic418967fa.accept_13_7_8_10_1_2663 72 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 179
  (Polychromatic418967fa.accept_19_14_4_8_1_8807 71 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 99 179 (accept_3_2 70 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  99 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 179 (accept_3_2 67 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 99 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 179
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 65 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 179 (accept_3_2 64 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  99 179 (Polychromatic418967fa.accept_13_11_8_10_1_676 63 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 179 (accept_3_2 61 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 179 (Polychromatic418967fa.accept_14_4_1_11_1_5026 60 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 99 179 (accept_3_2 58 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  99 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 179 (accept_3_2 55 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 179
  (Polychromatic418967fa.accept_15_8_9_14_1_4577 53 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 179 (accept_3_2 52 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  99 179 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 179 (accept_3_2 49 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 179 (Polychromatic418967fa.accept_18_12_9_17_1_7428 48 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 179 (accept_3_2 46 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  99 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 179 (accept_3_2 43 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 179 (Polychromatic418967fa.accept_15_12_9_14_1_2635 42 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 179
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 41 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 179 (accept_3_2 40 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 179 (Polychromatic418967fa.accept_17_5_14_9_1_5104 39 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 179 (accept_3_2 37 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 179 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 179
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 179 (accept_3_2 34 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 179 (accept_3_2 31 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 179 (Polychromatic418967fa.accept_13_4_8_10_1_671 30 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 179
  (Polychromatic418967fa.accept_17_12_14_9_1_5079 29 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 179 (accept_3_2 28 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 179 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 179 (accept_3_2 25 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 179
  (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 179 (accept_3_2 22 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 179 (accept_3_2 19 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 179 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 179 (accept_3_2 16 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 179 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 179 (accept_3_2 13 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 179
  (Polychromatic418967fa.accept_13_11_8_10_1_676 11 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 179 (accept_3_2 10 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 179 (accept_3_2 7 99 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 179 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 99 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 179 (accept_3_2 4 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 99 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 179 (accept_3_2 1 99 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 82 98 179 (Eq.refl Bool.true) (allA_succ_of_accept 81 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 81
  98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 179 (accept_3_2 79 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 179 (Polychromatic418967fa.accept_17_10_13_9_1_3913 78 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 179 (accept_3_2 76 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 179
  (Polychromatic418967fa.accept_10_4_8_9_1_784 74 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 179 (accept_3_2 73 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 179 (Polychromatic418967fa.accept_17_4_13_9_1_921 72 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 179 (Polychromatic418967fa.accept_10_1_8_9_1_787 71 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 179 (accept_3_2 70 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 179 (accept_3_2 67 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 179 (Polychromatic418967fa.accept_15_6_8_14_1_4575 66 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 179 (accept_3_2 64 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 179
  (Polychromatic418967fa.accept_11_7_10_3_1_633 62 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 179 (accept_3_2 61 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 179 (Polychromatic418967fa.accept_13_8_7_10_1_4362 60 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 179 (Polychromatic418967fa.accept_18_5_8_17_1_3478 59 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 179 (accept_3_2 58 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 179 (accept_3_2 55 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 179 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 179 (accept_3_2 52 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 179
  (Polychromatic418967fa.accept_15_5_8_14_1_432 50 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 179 (accept_3_2 49 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 179 (Polychromatic418967fa.accept_21_6_14_11_1_10103 48 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 179 (Polychromatic418967fa.accept_10_7_8_9_1_785 47 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 179 (accept_3_2 46 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 179
  (Polychromatic418967fa.accept_10_4_8_9_1_784 44 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 179 (accept_3_2 43 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 179 (Polychromatic418967fa.accept_13_3_7_10_1_668 42 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 179 (accept_3_2 40 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 179
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 38 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 179 (accept_3_2 37 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 179 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 179 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 179 (accept_3_2 34 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 179 (accept_3_2 31 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 179 (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 179 (accept_3_2 28 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 179
  (Polychromatic418967fa.accept_21_5_14_11_1_10102 26 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 98 179 (accept_3_2 25 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 98 179 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 98 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 98 179 (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 98
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 179 (accept_3_2 22 98 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 179 (accept_3_2 19 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 179 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 179 (accept_3_2 16 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 179
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 179 (accept_3_2 13 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 179 (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 179 (Polychromatic418967fa.accept_10_1_8_9_1_787 11 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 179 (accept_3_2 10 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 179 (accept_3_2 7 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  179 (Polychromatic418967fa.accept_15_6_8_14_1_4575 6 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 98 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 179 (accept_3_2 4 98 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 179
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 2 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 179 (accept_3_2 1 98 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 97 179 (Eq.refl
  Bool.true) (allA_of_3_0 83 97 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 96 179 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 96 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 96 179 (accept_3_2 82 96 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 179 (Polychromatic418967fa.accept_21_18_12_11_1_7078 81 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 179
  (Polychromatic418967fa.accept_13_2_5_10_1_250 80 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 96 179 (accept_3_2 79 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  96 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 96 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 179 (accept_3_2 76 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 96 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 96 179 (accept_3_2 73 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  96 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 96 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 179 (accept_3_2 70 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 96 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 96 179 (accept_3_2 67 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  96 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 96 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 179 (accept_3_2 64 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 96 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 96 179 (accept_3_2 61 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  96 179 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 96 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 179 (accept_3_2 58 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 96 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 96 179 (accept_3_2 55 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  96 179 (Polychromatic418967fa.accept_13_2_5_10_1_250 54 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 96 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 179 (accept_3_2 52 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 96 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 96 179 (accept_3_2 49 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  96 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 96 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 179 (accept_3_2 46 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 96 179 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 179 (accept_3_2 43 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  96 179 (Polychromatic418967fa.accept_17_8_11_9_1_5099 42 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 96 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 179 (accept_3_2 40 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 96 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 179 (accept_3_2 37 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  96 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 96 179 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 179 (accept_3_2 34 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 96 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 179 (accept_3_2 31 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  96 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 96 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 179 (accept_3_2 28 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 96 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 179
  (Polychromatic418967fa.accept_19_7_1_8_1_7300 26 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 179 (accept_3_2 25 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  96 179 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 96 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 179 (accept_3_2 22 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 96 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 179 (accept_3_2 19 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  96 179 (Polychromatic418967fa.accept_19_18_1_8_1_7291 18 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 96 179 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 179 (accept_3_2 16 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 179 (accept_3_2 13 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  96 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 96 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 179 (accept_3_2 10 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 179 (accept_3_2 7 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96
  179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 179 (accept_3_2 4 96 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 96 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  96 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 179 (accept_3_2 1 96 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 95 179 (Eq.refl
  Bool.true) (allA_succ_of_accept 84 95 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 83
  95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 179 (accept_3_2 82 95
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 179
  (Polychromatic418967fa.accept_10_1_5_9_1_157 81 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 95 179 (Polychromatic418967fa.accept_18_8_5_17_1_1388 80 95 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 179 (accept_3_2 79 95 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 95 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 179 (Polychromatic418967fa.accept_15_2_5_14_1_61
  77 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 179 (accept_3_2 76
  95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 95 179
  (Polychromatic418967fa.accept_9_3_5_8_1_99 75 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 95 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 95 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 179 (accept_3_2 73 95 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 95 179 (Polychromatic418967fa.accept_13_7_4_10_1_2675 72 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 179
  (Polychromatic418967fa.accept_10_1_5_9_1_157 71 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 179 (accept_3_2 70 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 68 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 179 (accept_3_2 67 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 179 (accept_3_2 64 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 179 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 179 (Polychromatic418967fa.accept_15_2_5_14_1_61 62 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 179 (accept_3_2 61 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 179
  (Polychromatic418967fa.accept_11_4_7_3_1_289 59 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 179 (accept_3_2 58 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 179 (accept_3_2 55 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 179 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 179
  (Polychromatic418967fa.accept_13_1_4_10_1_622 53 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 179 (accept_3_2 52 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 179 (Polychromatic418967fa.accept_13_11_4_10_1_3440 50 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 179 (accept_3_2 49 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 95 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 179 (accept_3_2 46 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 179 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 179 (accept_3_2 43 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 179
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 179 (accept_3_2 40 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 179 (accept_3_2 37 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 179
  (Polychromatic418967fa.accept_17_1_10_9_1_3884 35 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 179 (accept_3_2 34 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 179 (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 179 (accept_3_2 31 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 95 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 179 (accept_3_2 28 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 179 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 179 (Polychromatic418967fa.accept_10_6_5_9_1_1233 26 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 179 (accept_3_2 25 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 179
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 179 (accept_3_2 22 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 179 (accept_3_2 19 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 179 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 179
  (Polychromatic418967fa.accept_15_2_5_14_1_61 17 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 179 (accept_3_2 16 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 179 (Polychromatic418967fa.accept_10_4_5_9_1_1231 14 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 179 (accept_3_2 13 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 179 (accept_3_2 10 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 179 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 179 (Polychromatic418967fa.accept_13_8_4_10_1_4358 8 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 179 (accept_3_2 7 95 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 95 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 179
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 179 (accept_3_2 4 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  179 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 95 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 95 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 179 (accept_3_2 1 95 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 86 94 179 (Eq.refl Bool.true) (allA_of_3_0 86 94 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  87 93 179 (Eq.refl Bool.true) (allA_succ_of_accept 86 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 93 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 179 (accept_3_2 85 93 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 93 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262
  84 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 179
  (Polychromatic418967fa.accept_7_6_2_4_1_291 83 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 93 179 (accept_3_2 82 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  93 179 (Polychromatic418967fa.accept_13_3_2_10_1_2697 81 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 93 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 93 179 (accept_3_2 79 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 93 179 (accept_3_2 76 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  93 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 179 (accept_3_2 73 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 93 179 (Polychromatic418967fa.accept_14_2_9_11_1_3054 72 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 179
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 71 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 179 (accept_3_2 70 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  93 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 93 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 179 (accept_3_2 67 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 93 179 (accept_3_2 64 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  93 179 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 179 (accept_3_2 61 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 93 179 (accept_3_2 58 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  93 179 (Polychromatic418967fa.accept_13_5_2_10_1_248 57 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 93 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 179 (accept_3_2 55 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 179
  (Polychromatic418967fa.accept_19_15_17_8_1_10101 53 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 93 179 (accept_3_2 52 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 93 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 93 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 93 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 179 (accept_3_2 49 93 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 48
  93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 179 (accept_3_2 46 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  93 179 (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 93 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 179 (accept_3_2 43 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 179
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 179 (accept_3_2 40 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  93 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 179 (accept_3_2 37 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 179 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 179
  (Polychromatic418967fa.accept_17_1_8_9_1_1810 35 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 179 (accept_3_2 34 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  93 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 93 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 179 (accept_3_2 31 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 179 (accept_3_2 28 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 179 (accept_3_2 25 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 179 (accept_3_2 22 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 179 (Polychromatic418967fa.accept_13_8_2_10_1_652 21 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 179 (accept_3_2 19 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 179
  (Polychromatic418967fa.accept_15_2_3_14_1_972 17 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 179 (accept_3_2 16 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 179 (accept_3_2 13 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 179 (accept_3_2 10 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 179 (Polychromatic418967fa.accept_19_9_17_8_1_2075 9 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 179 (accept_3_2 7 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 179 (accept_3_2 4 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  179 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 93 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 93 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 179 (accept_3_2 1 93 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 93
  179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 92 179
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 179 (accept_3_2 85 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 179 (Polychromatic418967fa.accept_17_15_7_9_1_1809 83 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 179 (accept_3_2 82 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 179 (accept_3_2 79 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 179 (accept_3_2 76 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 179 (accept_3_2 73 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 179 (Polychromatic418967fa.accept_15_12_2_14_1_5659 72 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 71 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 179 (accept_3_2 70 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 179 (accept_3_2 67 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 179 (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 179 (accept_3_2 64 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 179
  (Polychromatic418967fa.accept_11_7_4_3_1_302 62 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 179 (accept_3_2 61 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 179 (accept_3_2 58 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 179
  (Polychromatic418967fa.accept_13_4_1_10_1_693 56 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 179 (accept_3_2 55 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 179 (Polychromatic418967fa.accept_17_2_7_9_1_2796 53 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 179 (accept_3_2 52 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 179 (accept_3_2 49 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 179 (accept_3_2 46 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 179
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 44 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 179 (accept_3_2 43 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 179 (accept_3_2 40 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 179 (accept_3_2 37 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 179 (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 179 (Polychromatic418967fa.accept_13_9_1_10_1_647 35 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 179 (accept_3_2 34 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 179 (accept_3_2 31 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 179 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 179 (accept_3_2 28 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 179 (accept_3_2 25 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 179 (accept_3_2 22 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 179
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 179 (accept_3_2 19 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 179 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 179 (accept_3_2 16 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 179 (accept_3_2 13 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 179 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 179 (accept_3_2 10 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 179
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 8 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 179 (accept_3_2 7 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  179 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 92 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 179 (accept_3_2 4 92 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  92 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 179 (accept_3_2 1 92 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 91 179
  (Eq.refl Bool.true) (allA_of_3_0 89 91 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 179
  (allA_succ_of_accept 89 90 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 179 (accept_3_2 88 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 86
  90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 179 (accept_3_2 85 90
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 179
  (Polychromatic418967fa.accept_13_6_12_10_1_690 84 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 179 (Polychromatic418967fa.accept_19_7_14_8_1_4535 83 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 179 (accept_3_2 82 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 80
  90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 179 (accept_3_2 79 90
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 179
  (Polychromatic418967fa.accept_11_1_2_3_1_688 78 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 90 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 179 (accept_3_2 76 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 179 (Polychromatic418967fa.accept_13_9_12_10_1_242
  74 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 179 (accept_3_2 73
  90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 90 179 (Polychromatic418967fa.accept_13_6_12_10_1_690 71 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 179 (accept_3_2 70 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 68
  90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 179 (accept_3_2 67 90
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 179 (Polychromatic418967fa.accept_7_3_6_4_1_30
  66 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 179 (accept_3_2 64 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  90 179 (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 90 179 (Polychromatic418967fa.accept_19_5_14_8_1_5944 62 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 179 (accept_3_2 61 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 179 (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 90
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 179
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 179 (accept_3_2 58 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  90 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 90 179 (Polychromatic418967fa.accept_11_1_2_3_1_688 56 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 179 (accept_3_2 55 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 179 (accept_3_2 52 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  90 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 90 179 (Polychromatic418967fa.accept_13_11_12_10_1_2652 50 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 179 (accept_3_2 49 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 179 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 90
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 179 (accept_3_2 46 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  90 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 90 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 179 (accept_3_2 43 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 179 (Polychromatic418967fa.accept_19_4_14_8_1_4510 42 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 179 (accept_3_2 40 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  90 179 (Polychromatic418967fa.accept_16_7_10_3_1_2210 39 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 179 (accept_3_2 37 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 179 (Polychromatic418967fa.accept_20_16_10_19_1_10100 36 90 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 179
  (Polychromatic418967fa.accept_13_9_12_10_1_242 35 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 179 (accept_3_2 34 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 179 (Polychromatic418967fa.accept_13_6_12_10_1_690 32 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 179 (accept_3_2 31 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 90 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 179 (accept_3_2 28 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  90 179 (Polychromatic418967fa.accept_20_7_10_19_1_8724 27 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 90 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 179 (accept_3_2 25 90 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 179 (accept_3_2 22 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 179 (Polychromatic418967fa.accept_13_7_12_10_1_640 20 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 179 (accept_3_2 19 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 179 (Polychromatic418967fa.accept_21_18_6_11_1_7031 18 90
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 179 (accept_3_2 16 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 179 (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 179 (Polychromatic418967fa.accept_17_14_5_9_1_7766 14 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 179 (accept_3_2 13 90 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 90 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 179
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 90 179 (accept_3_2 10 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 90 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 179 (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 90 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 179 (accept_3_2 7 90 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 179 (Polychromatic418967fa.accept_13_6_12_10_1_690
  6 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 179 (accept_3_2 4 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90
  179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 179 (accept_3_2 1 90 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 90 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 89 179 (allA_succ_of_accept 88 89 179 (accept_3_2 88 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 179 (Polychromatic418967fa.accept_16_7_9_3_1_1324 87 89 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 179 (accept_3_2 85 89 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 179 (Polychromatic418967fa.accept_20_4_9_19_1_766
  84 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 179 (accept_3_2 82 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 179 (Polychromatic418967fa.accept_13_3_11_10_1_2647 81 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 179 (Polychromatic418967fa.accept_13_2_11_10_1_1881 80 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 179 (accept_3_2 79 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 179
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 77 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 89 179 (accept_3_2 76 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 89 179 (Polychromatic418967fa.accept_19_18_13_8_1_10099 75 89 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 179 (accept_3_2 73 89 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 72
  89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 179 (accept_3_2 70 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 179 (Polychromatic418967fa.accept_11_2_1_3_1_683 68 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 179 (accept_3_2 67 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 179 (accept_3_2 64 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 179 (Polychromatic418967fa.accept_17_12_4_9_1_3889 63 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 179 (accept_3_2 61 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 179 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 179
  (Polychromatic418967fa.accept_19_2_13_8_1_8778 59 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 179 (accept_3_2 58 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 179 (Polychromatic418967fa.accept_13_4_11_10_1_1226 56 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 179 (accept_3_2 55 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 179
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 53 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 179 (accept_3_2 52 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 179 (accept_3_2 49 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 179
  (Polychromatic418967fa.accept_13_8_11_10_1_636 47 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 179 (accept_3_2 46 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 179 (Polychromatic418967fa.accept_27_18_8_17_1_10098 45 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 179 (accept_3_2 43 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 179 (accept_3_2 40 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 179 (Polychromatic418967fa.accept_16_7_9_3_1_1324 39 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 179 (accept_3_2 37 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 179
  (Polychromatic418967fa.accept_11_2_1_3_1_683 35 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 179 (accept_3_2 34 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 179 (Polychromatic418967fa.accept_19_14_13_8_1_5943 33 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 179 (Polychromatic418967fa.accept_20_12_9_19_1_10097 32 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 179 (accept_3_2 31 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 179 (accept_3_2 28 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 179 (accept_3_2 25 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 179 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 179 (accept_3_2 22 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 179 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 179 (accept_3_2 19 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 179
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 179 (accept_3_2 16 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 179 (accept_3_2 13 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 179 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 89 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 179
  (Polychromatic418967fa.accept_22_11_1_3_1_10096 11 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 179 (accept_3_2 10 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 179 (accept_3_2 7 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 179
  (Polychromatic418967fa.accept_19_5_13_8_1_3229 5 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 179 (accept_3_2 4 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  179 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 89 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 179 (accept_3_2 1 89 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89
  179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 179
  (allA_of_3_0 88 88 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 179 (allA_succ_of_accept 86 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 87 179 (accept_3_2 85 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  87 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 87 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 179 (accept_3_2 82 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 179 (accept_3_2 79 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 179 (accept_3_2 76 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 179 (accept_3_2 73 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 179 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 179 (accept_3_2 70 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 179 (accept_3_2 67 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 179 (accept_3_2 64 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 179 (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 179 (accept_3_2 61 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 179 (accept_3_2 58 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 179 (accept_3_2 55 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 179 (Polychromatic418967fa.accept_15_9_12_14_1_963 54 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 179 (Polychromatic418967fa.accept_13_1_9_10_1_625 53 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 179 (accept_3_2 52 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 179 (Polychromatic418967fa.accept_11_7_10_3_1_633 51 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 179 (accept_3_2 49 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 179 (accept_3_2 46 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 179 (accept_3_2 43 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 179 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 179 (accept_3_2 40 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 179 (accept_3_2 37 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 179 (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 179 (accept_3_2 34 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 87
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 179 (accept_3_2 31 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 179 (accept_3_2 28 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 179 (accept_3_2 25 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 179 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 179 (accept_3_2 22 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 179 (accept_3_2 19 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 179 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 179 (Polychromatic418967fa.accept_15_2_12_14_1_1709 17 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 179 (accept_3_2 16 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 179 (accept_3_2 13 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 179 (accept_3_2 10 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 87 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 179 (accept_3_2 7 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 87 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 179 (accept_3_2 4 87 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 179 (accept_3_2 1 87 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 179
  (allA_succ_of_accept 85 86 179 (accept_3_2 85 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 179 (accept_3_2 82 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 179 (accept_3_2 79 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 179 (accept_3_2 76 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 179 (accept_3_2 73 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 179 (Polychromatic418967fa.accept_11_6_9_3_1_1103 72 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 179 (Polychromatic418967fa.accept_17_3_1_9_1_9012 71 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 179 (accept_3_2 70 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 179 (accept_3_2 67 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 179 (accept_3_2 64 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 179
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 179 (accept_3_2 61 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 179 (Polychromatic418967fa.accept_13_7_8_10_1_2663 59 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 179 (accept_3_2 58 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 179 (accept_3_2 55 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 179 (accept_3_2 52 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 179
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 50 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 179 (accept_3_2 49 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 179 (accept_3_2 46 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 179 (accept_3_2 43 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 179 (accept_3_2 40 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 179 (accept_3_2 37 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 179 (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 179 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 179 (accept_3_2 34 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 179 (accept_3_2 31 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 179 (accept_3_2 28 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 179 (accept_3_2 25 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 179 (accept_3_2 22 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 179
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 179 (accept_3_2 19 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 179 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 179 (accept_3_2 16 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 179
  (Polychromatic418967fa.accept_20_14_6_19_1_10095 14 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 86 179 (accept_3_2 13 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 86 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 86 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 86 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 179 (accept_3_2 10 86 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 179 (accept_3_2 7 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 86 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 179 (accept_3_2 4 86 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 86
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 179 (accept_3_2 1 86 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 179
  (allA_of_3_0 85 85 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 179 (allA_succ_of_accept 83 84 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 179 (accept_3_2 82 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 179 (Polychromatic418967fa.accept_11_4_7_3_1_289 81 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 179 (Polychromatic418967fa.accept_13_2_6_10_1_2703 80 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 179 (accept_3_2 79 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 84 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 179 (accept_3_2 76 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 179 (Polychromatic418967fa.accept_10_5_4_9_1_420 75 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 179 (accept_3_2 73 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 179 (Polychromatic418967fa.accept_15_12_9_14_1_2635 72 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 179
  (Polychromatic418967fa.accept_8_7_4_3_1_156 71 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 179 (accept_3_2 70 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 179 (accept_3_2 67 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 179 (Polychromatic418967fa.accept_15_6_9_14_1_3457 66 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 179 (accept_3_2 64 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 179 (Polychromatic418967fa.accept_20_2_4_19_1_5634 62 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 179 (accept_3_2 61 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 84 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 179 (accept_3_2 58 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 179 (Polychromatic418967fa.accept_13_5_6_10_1_2659 57 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 179 (accept_3_2 55 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 179 (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 179
  (Polychromatic418967fa.accept_10_3_4_9_1_15 53 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 179 (accept_3_2 52 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 179 (accept_3_2 49 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 179
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 179 (accept_3_2 46 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 179 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 179 (Polychromatic418967fa.accept_13_5_6_10_1_2659 44 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 179 (accept_3_2 43 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 84 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 179 (accept_3_2 40 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 179 (accept_3_2 37 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 179 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 179
  (Polychromatic418967fa.accept_10_5_4_9_1_420 35 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 179 (accept_3_2 34 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 179 (accept_3_2 31 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 179 (Polychromatic418967fa.accept_13_4_6_10_1_1199 30 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 179 (accept_3_2 28 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 179 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 179 (Polychromatic418967fa.accept_11_4_7_3_1_289 26 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 179 (accept_3_2 25 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 179
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 179 (accept_3_2 22 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 179 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 179 (accept_3_2 19 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 179
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 179 (accept_3_2 16 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 179 (accept_3_2 13 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 179 (Polychromatic418967fa.accept_13_12_6_10_1_667 12 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 179 (accept_3_2 10 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 179 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 179 (accept_3_2 7 84 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 84 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 179 (accept_3_2 4 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  179 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 84 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 84 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 179 (accept_3_2 1 84 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 179 (allA_succ_of_accept 82 83 179 (accept_3_2 82 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 179 (Polychromatic418967fa.accept_15_6_8_14_1_4575 81 83 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 83 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 179 (accept_3_2 79 83 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 78
  83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 179 (accept_3_2 76 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 74 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 179 (accept_3_2 73 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 179
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 71 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 179 (accept_3_2 70 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 179 (accept_3_2 67 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 179 (accept_3_2 64 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 179 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 179 (Polychromatic418967fa.accept_20_2_3_19_1_8730 62 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 179 (accept_3_2 61 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 83 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 179
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 179 (accept_3_2 58 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 179 (Polychromatic418967fa.accept_10_6_3_9_1_1207 56 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 179 (accept_3_2 55 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 179
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 53 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 179 (accept_3_2 52 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 179 (accept_3_2 49 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 179 (accept_3_2 46 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 179 (accept_3_2 43 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 179 (accept_3_2 40 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 179 (accept_3_2 37 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 179 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 179
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 179 (accept_3_2 34 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 179 (accept_3_2 31 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 179
  (Polychromatic418967fa.accept_20_9_3_19_1_10094 29 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 179 (accept_3_2 28 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 179 (Polychromatic418967fa.accept_21_6_20_11_1_7067 27 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 179 (accept_3_2 25 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 179 (accept_3_2 22 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 179 (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 179 (accept_3_2 19 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 179 (Polychromatic418967fa.accept_17_1_15_9_1_1743 18 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 179
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 179 (accept_3_2 16 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 179 (accept_3_2 13 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 179
  (Polychromatic418967fa.accept_19_11_7_8_1_2110 11 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 179 (accept_3_2 10 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 179 (Polychromatic418967fa.accept_11_8_6_3_1_661 8 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 179 (accept_3_2 7 83 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 179 (accept_3_2 4 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 83 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 83 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 179 (accept_3_2 1 83 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 179 (allA_of_3_0 82 82 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 179
  (allA_succ_of_accept 80 81 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 179 (accept_3_2 79 81 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 179 (Polychromatic418967fa.accept_16_13_1_3_1_2205
  77 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 179 (accept_3_2 76
  81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 179
  (Polychromatic418967fa.accept_10_5_1_9_1_791 75 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 81 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 179 (accept_3_2 73 81 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 179 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 179 (Polychromatic418967fa.accept_13_6_3_10_1_698
  71 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 179 (accept_3_2 70
  81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 179
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 69 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 179 (accept_3_2 67 81 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 179 (Polychromatic418967fa.accept_10_5_1_9_1_791
  65 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 179 (accept_3_2 64
  81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 179
  (Polychromatic418967fa.accept_12_3_9_11_1_231 63 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 179 (accept_3_2 61 81 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 179 (Polychromatic418967fa.accept_19_3_5_8_1_8790 60 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 179 (Polychromatic418967fa.accept_13_7_3_10_1_656
  59 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 179 (accept_3_2 58
  81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 179
  (Polychromatic418967fa.accept_28_1_25_11_1_10093 57 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 179 (accept_3_2 55 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 179
  (Polychromatic418967fa.accept_15_8_6_14_1_975 53 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 179 (accept_3_2 52 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 179 (Polychromatic418967fa.accept_11_7_4_3_1_302 51 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 179 (accept_3_2 49 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 179 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 81 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 179
  (Polychromatic418967fa.accept_21_5_18_11_1_7041 47 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 179 (accept_3_2 46 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 179 (accept_3_2 43 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 179
  (Polychromatic418967fa.accept_13_2_3_10_1_658 41 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 179 (accept_3_2 40 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 179 (accept_3_2 37 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 179 (Polychromatic418967fa.accept_16_4_1_3_1_6581 36 81 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 179
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 179 (accept_3_2 34 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 179 (Polychromatic418967fa.accept_13_7_3_10_1_656 33 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 179 (accept_3_2 31 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 179
  (Polychromatic418967fa.accept_11_7_4_3_1_302 29 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 179 (accept_3_2 28 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 179 (accept_3_2 25 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 179 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 81 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 179
  (Polychromatic418967fa.accept_15_8_6_14_1_975 23 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 179 (accept_3_2 22 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 179 (Polychromatic418967fa.accept_17_4_13_9_1_921 21 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 179 (accept_3_2 19 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 179
  (Polychromatic418967fa.accept_23_17_12_18_1_10092 17 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 81 179 (accept_3_2 16 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 81 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 81 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 179 (accept_3_2 13 81 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 179 (Polychromatic418967fa.accept_10_2_1_9_1_1248
  12 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 179
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 179 (accept_3_2 10 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 179 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 179 (accept_3_2 7 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 179
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 179 (accept_3_2 4 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  179 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 81 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 81 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 179 (accept_3_2 1 81 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 81 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 179 (allA_succ_of_accept 79 80 179 (accept_3_2 79 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 80 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 179 (Polychromatic418967fa.accept_13_12_2_10_1_2698 77 80
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 179 (accept_3_2 76 80 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 75
  80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 179 (accept_3_2 73 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 179 (Polychromatic418967fa.accept_17_4_12_9_1_6379 72 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 179 (accept_3_2 70 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 179
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 68 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 179 (accept_3_2 67 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 179 (Polychromatic418967fa.accept_15_6_5_14_1_429 66 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 179 (Polychromatic418967fa.accept_17_14_12_9_1_2774 65 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 179 (accept_3_2 64 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 179
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 179 (accept_3_2 61 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 179 (Polychromatic418967fa.accept_13_8_2_10_1_652 60 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 179 (Polychromatic418967fa.accept_18_5_8_17_1_3478 59 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 179 (accept_3_2 58 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 179
  (Polychromatic418967fa.accept_17_5_12_9_1_10091 56 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 179 (accept_3_2 55 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 179 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 179 (Polychromatic418967fa.accept_15_8_5_14_1_986 53 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 179 (accept_3_2 52 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 179 (accept_3_2 49 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 179 (Polychromatic418967fa.accept_13_8_2_10_1_652 47 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 179 (accept_3_2 46 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 179
  (Polychromatic418967fa.accept_13_5_2_10_1_248 44 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 179 (accept_3_2 43 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 179 (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 179 (accept_3_2 40 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 179 (accept_3_2 37 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 179 (Polychromatic418967fa.accept_14_7_10_11_1_8112 35 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 179 (accept_3_2 34 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 179
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 32 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 179 (accept_3_2 31 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 179 (Polychromatic418967fa.accept_23_7_11_18_1_6779 30 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 179 (accept_3_2 28 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 179 (accept_3_2 25 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 179 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 179 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 179 (accept_3_2 22 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 179
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 179 (accept_3_2 19 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 179 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 179 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 179 (accept_3_2 16 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 179 (accept_3_2 13 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 179 (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 179 (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 179 (accept_3_2 10 80 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 179 (accept_3_2 7 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 179 (Polychromatic418967fa.accept_13_5_2_10_1_248 5 80 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 179 (accept_3_2 4 80 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  80 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 179 (accept_3_2 1 80 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 179 (allA_of_3_0 79
  79 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 179 (allA_succ_of_accept 77 78 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 179 (accept_3_2 76 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 179 (accept_3_2 73 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 179 (Polychromatic418967fa.accept_19_15_2_8_1_7263 72 78 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 179
  (Polychromatic418967fa.accept_10_1_8_9_1_787 71 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 179 (accept_3_2 70 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 179 (accept_3_2 67 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 78 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 179 (accept_3_2 64 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 179 (Polychromatic418967fa.accept_19_6_2_8_1_4496 63 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 179 (Polychromatic418967fa.accept_15_2_3_14_1_972 62 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 179 (accept_3_2 61 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 179 (Polychromatic418967fa.accept_14_4_8_11_1_794 60 78 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 179 (accept_3_2 58 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 179 (accept_3_2 55 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 78 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 179 (accept_3_2 52 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 179 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 179 (accept_3_2 49 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 78 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 179 (accept_3_2 46 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 179 (Polychromatic418967fa.accept_10_4_8_9_1_784 44 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 179 (accept_3_2 43 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 179 (Polychromatic418967fa.accept_24_18_6_11_1_10090 42 78 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 179 (accept_3_2 40 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 179 (accept_3_2 37 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 179 (Polychromatic418967fa.accept_22_14_12_3_1_10089 36 78 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 179
  (Polychromatic418967fa.accept_11_2_1_3_1_683 35 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 179 (accept_3_2 34 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 179 (accept_3_2 31 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 78 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 179 (accept_3_2 28 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 179 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 179 (accept_3_2 25 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 78 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 179 (accept_3_2 22 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 179 (accept_3_2 19 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 179 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 78 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 179 (accept_3_2 16 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 179 (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 179 (accept_3_2 13 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 78 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 179 (accept_3_2 10 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 179 (Polychromatic418967fa.accept_23_8_9_18_1_5035 8 78 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 179 (accept_3_2 7 78 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 179 (Polychromatic418967fa.accept_19_6_2_8_1_4496 6 78 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 179 (accept_3_2 4 78 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 179 (accept_3_2 1 78 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 179
  (allA_succ_of_accept 76 77 179 (accept_3_2 76 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 179 (accept_3_2 73 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 179 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 179
  (Polychromatic418967fa.accept_13_6_12_10_1_690 71 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 179 (accept_3_2 70 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 179 (Polychromatic418967fa.accept_10_8_7_9_1_425 68 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 179 (accept_3_2 67 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 179 (accept_3_2 64 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 179 (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 179 (accept_3_2 61 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 179
  (Polychromatic418967fa.accept_13_7_12_10_1_640 59 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 179 (accept_3_2 58 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 179 (accept_3_2 55 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 179
  (Polychromatic418967fa.accept_19_15_1_8_1_4520 53 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 179 (accept_3_2 52 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 179 (accept_3_2 49 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 179 (accept_3_2 46 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 179 (Polychromatic418967fa.accept_13_6_12_10_1_690 45 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 179 (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 179 (accept_3_2 43 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 179
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 41 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 179 (accept_3_2 40 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 179 (accept_3_2 37 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 179 (Polychromatic418967fa.accept_20_16_17_19_1_8721 36 77 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 179
  (Polychromatic418967fa.accept_13_9_12_10_1_242 35 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 179 (accept_3_2 34 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 179 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 179 (accept_3_2 31 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 179 (accept_3_2 28 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 179 (Polychromatic418967fa.accept_15_12_2_14_1_5659 27 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 179 (accept_3_2 25 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 179
  (Polychromatic418967fa.accept_21_2_14_11_1_7060 23 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 179 (accept_3_2 22 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 179 (accept_3_2 19 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 179
  (Polychromatic418967fa.accept_14_3_7_11_1_765 17 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 179 (accept_3_2 16 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 179 (accept_3_2 13 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 179 (accept_3_2 10 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 179 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 179 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 179 (accept_3_2 7 77 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 179
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 179 (accept_3_2 4 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  179 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 77 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 179 (accept_3_2 1 77 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 179 (allA_of_3_0 76 76 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 179 (allA_succ_of_accept 74 75
  179 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 179 (accept_3_2 73 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 179 (accept_3_2 70 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 179 (accept_3_2 67 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 179 (Polychromatic418967fa.accept_10_6_5_9_1_1233 66 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 179 (accept_3_2 64 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 179 (Polychromatic418967fa.accept_16_15_11_3_1_2179 63 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 179 (accept_3_2 61 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 179 (accept_3_2 58 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 179 (accept_3_2 55 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 179 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 179 (Polychromatic418967fa.accept_17_2_7_9_1_2796 53 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 179 (accept_3_2 52 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 179 (accept_3_2 49 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 179 (accept_3_2 46 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 179 (accept_3_2 43 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 179 (accept_3_2 40 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 179 (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 179 (accept_3_2 37 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 179 (Polychromatic418967fa.accept_19_16_18_8_1_8784 35 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 179 (accept_3_2 34 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 179 (accept_3_2 31 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 179 (accept_3_2 28 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 179 (accept_3_2 25 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 179 (accept_3_2 22 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 179 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 179 (accept_3_2 19 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 179 (Polychromatic418967fa.accept_21_18_12_11_1_7078 18 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 179 (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 179 (accept_3_2 16 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 179 (accept_3_2 13 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 179 (Polychromatic418967fa.accept_22_12_9_3_1_10088 12 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 179 (accept_3_2 10 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 179 (accept_3_2 7 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 75 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 179 (accept_3_2 4 75 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 179 (Polychromatic418967fa.accept_21_3_12_11_1_7034 3 75 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 179 (accept_3_2 1 75 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 179 (allA_succ_of_accept
  73 74 179 (accept_3_2 73 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 179
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 72 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 179 (Polychromatic418967fa.accept_11_5_8_3_1_66 71 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 179 (accept_3_2 70 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 68
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 179 (accept_3_2 67 74
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 66 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 179 (accept_3_2 64 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 179 (Polychromatic418967fa.accept_18_8_2_17_1_4782
  62 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 179 (accept_3_2 61
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 179
  (Polychromatic418967fa.accept_9_6_2_8_1_592 60 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 179 (accept_3_2 58 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 179 (Polychromatic418967fa.accept_12_8_2_11_1_246
  56 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 179 (accept_3_2 55
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 179
  (Polychromatic418967fa.accept_17_3_6_9_1_2761 54 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 179 (accept_3_2 52 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 50
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 179 (accept_3_2 49 74
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 48 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 179 (Polychromatic418967fa.accept_18_11_2_17_1_3490 47 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 179 (accept_3_2 46 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 179 (Polychromatic418967fa.accept_12_8_2_11_1_246
  44 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 179 (accept_3_2 43
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 179
  (Polychromatic418967fa.accept_9_6_2_8_1_592 42 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 179 (accept_3_2 40 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  38 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 179 (accept_3_2 37
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 179
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 74 179 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 179 (accept_3_2 34 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 32
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 179 (accept_3_2 31 74
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 30 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 179 (accept_3_2 28 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 74 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 179 (Polychromatic418967fa.accept_18_8_2_17_1_4782
  26 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 179 (accept_3_2 25
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 179
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 74 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 179 (accept_3_2 22 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 179 (Polychromatic418967fa.accept_12_8_2_11_1_246
  20 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 179 (accept_3_2 19
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 179
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 179 (accept_3_2 16 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 74 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 179 (accept_3_2 13 74
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 74 179 (Polychromatic418967fa.accept_18_11_2_17_1_3490 11 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 179 (accept_3_2 10 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 74 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 179 (accept_3_2 7 74 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 179 (accept_3_2 4 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 179 (Polychromatic418967fa.accept_23_2_5_18_1_6732 2 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 179 (accept_3_2 1 74 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  179 (allA_of_3_0 73 73 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 179 (allA_succ_of_accept 71 72 179
  (Polychromatic418967fa.accept_10_1_2_9_1_152 71 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 179 (accept_3_2 70 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 179 (accept_3_2 67 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 179 (Polychromatic418967fa.accept_23_20_3_18_1_10087 66 72 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 179
  (Polychromatic418967fa.accept_14_9_2_11_1_780 65 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 179 (accept_3_2 64 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 179 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 179 (accept_3_2 61 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 179 (Polychromatic418967fa.accept_13_8_7_10_1_4362 60 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 179
  (Polychromatic418967fa.accept_16_11_8_3_1_3183 59 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 179 (accept_3_2 58 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 179 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 179 (Polychromatic418967fa.accept_13_4_7_10_1_1200 56 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 179 (accept_3_2 55 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 72 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 179
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 53 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 179 (accept_3_2 52 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 179 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 179 (Polychromatic418967fa.accept_19_12_15_8_1_10070 50 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 179 (accept_3_2 49 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 72 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 179 (accept_3_2 46 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 179 (Polychromatic418967fa.accept_16_13_8_3_1_5374 45 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 179 (Polychromatic418967fa.accept_16_12_8_3_1_4241 44 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 179 (accept_3_2 43 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 179 (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 72 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 179
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 179 (accept_3_2 40 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 179 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 179 (Polychromatic418967fa.accept_13_12_7_10_1_2662 38 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 179 (accept_3_2 37 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 179 (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 72 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 179
  (Polychromatic418967fa.accept_19_16_15_8_1_10086 35 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 72 179 (accept_3_2 34 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 72 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 179 (Polychromatic418967fa.accept_15_2_12_14_1_1709 32 72
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 179 (accept_3_2 31 72 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 179 (Polychromatic418967fa.accept_11_8_6_3_1_661
  30 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 179
  (Polychromatic418967fa.accept_13_3_7_10_1_668 29 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 179 (accept_3_2 28 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 179 (accept_3_2 25 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 179 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 179
  (Polychromatic418967fa.accept_14_9_2_11_1_780 23 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 179 (accept_3_2 22 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 179 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 179 (accept_3_2 19 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 179 (Polychromatic418967fa.accept_21_18_9_11_1_7082 18 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 179
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 179 (accept_3_2 16 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 179 (Polychromatic418967fa.accept_21_15_9_11_1_5417 15 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 179 (Polychromatic418967fa.accept_17_14_4_9_1_2792 14 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 179 (accept_3_2 13 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 72 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 179
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 179 (accept_3_2 10 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 179 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 179 (Polychromatic418967fa.accept_11_8_6_3_1_661 8 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 179 (accept_3_2 7 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 72 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 179 (accept_3_2 4 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  179 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 72 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 72 179 (Polychromatic418967fa.accept_15_2_12_14_1_1709 2 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 179 (accept_3_2 1 72 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 179 (allA_succ_of_accept 70 71 179 (accept_3_2 70 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 179 (Polychromatic418967fa.accept_13_4_6_10_1_1199 69 71 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 71 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 179 (accept_3_2 67 71 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 66
  71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 179
  (Polychromatic418967fa.accept_10_5_1_9_1_791 65 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 179 (accept_3_2 64 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 179 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 179 (Polychromatic418967fa.accept_10_2_1_9_1_1248 62 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 179 (accept_3_2 61 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 179 (accept_3_2 58 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 179 (Polychromatic418967fa.accept_13_5_6_10_1_2659 57 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 179 (Polychromatic418967fa.accept_13_4_6_10_1_1199 56 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 179 (accept_3_2 55 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 71 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 179
  (Polychromatic418967fa.accept_22_9_5_3_1_10085 53 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 179 (accept_3_2 52 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 179 (Polychromatic418967fa.accept_13_12_6_10_1_667 51 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 179 (Polychromatic418967fa.accept_20_10_11_19_1_10084 50 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 179 (accept_3_2 49 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 179 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 71 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 179 (accept_3_2 46 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 179 (accept_3_2 43 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 179 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 179
  (Polychromatic418967fa.accept_11_8_5_3_1_694 41 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 179 (accept_3_2 40 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 179 (Polychromatic418967fa.accept_21_18_8_11_1_10083 39 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 179 (accept_3_2 37 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 179
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 179 (accept_3_2 34 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 179 (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 179 (accept_3_2 31 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 179 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 179
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 29 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 179 (accept_3_2 28 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 179 (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 179 (accept_3_2 25 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 179
  (Polychromatic418967fa.accept_17_6_3_9_1_7739 23 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 179 (accept_3_2 22 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 179 (Polychromatic418967fa.accept_19_2_14_8_1_3273 21 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 179 (accept_3_2 19 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 179 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 179 (accept_3_2 16 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 179 (Polychromatic418967fa.accept_21_14_8_11_1_10082 14 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 179 (accept_3_2 13 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 179
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 11 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 179 (accept_3_2 10 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 179 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 179 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 179 (accept_3_2 7 71 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 179 (Polychromatic418967fa.accept_17_6_3_9_1_7739 6 71 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 179 (accept_3_2 4 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 71 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 179 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 71 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 179 (accept_3_2 1 71 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 179
  (allA_of_3_0 70 70 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 179 (allA_succ_of_accept 68 69 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 179 (accept_3_2 67 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 179 (accept_3_2 64 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 179 (accept_3_2 61 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 179 (Polychromatic418967fa.accept_13_8_4_10_1_4358 60 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 179 (accept_3_2 58 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 179 (accept_3_2 55 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 179 (Polychromatic418967fa.accept_13_1_4_10_1_622 53 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 179 (accept_3_2 52 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 179 (accept_3_2 49 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 179 (accept_3_2 46 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 179 (accept_3_2 43 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 179 (accept_3_2 40 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 179 (accept_3_2 37 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 179 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 179 (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 179 (accept_3_2 34 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 179 (accept_3_2 31 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 179 (accept_3_2 28 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 179 (accept_3_2 25 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 179 (accept_3_2 22 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 179 (accept_3_2 19 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 179 (accept_3_2 16 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 179 (accept_3_2 13 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 179 (accept_3_2 10 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 179 (accept_3_2 7 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 179 (accept_3_2 4 69 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 179 (accept_3_2 1 69 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 179 (allA_succ_of_accept 67 68
  179 (accept_3_2 67 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 179
  (Polychromatic418967fa.accept_9_3_5_8_1_99 66 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 68 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 179 (accept_3_2 64 68 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 62
  68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 179 (accept_3_2 61 68
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 179
  (Polychromatic418967fa.accept_9_6_5_8_1_598 60 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 179 (Polychromatic418967fa.accept_13_7_3_10_1_656 59 68 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 179 (accept_3_2 58 68 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 179 (accept_3_2 55 68
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 179
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 179 (Polychromatic418967fa.accept_27_26_14_17_1_10081 53 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 179 (accept_3_2 52 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 179 (accept_3_2 49 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 179 (accept_3_2 46 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 179 (accept_3_2 43 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 179 (accept_3_2 40 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 179 (accept_3_2 37 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 179 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 179 (accept_3_2 34 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 179
  (Polychromatic418967fa.accept_13_6_3_10_1_698 32 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 179 (accept_3_2 31 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 179 (accept_3_2 28 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 179 (accept_3_2 25 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 179 (accept_3_2 22 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 179 (accept_3_2 19 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 179 (Polychromatic418967fa.accept_19_18_11_8_1_10080 18 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 179 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 179 (accept_3_2 16 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 179
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 179 (accept_3_2 13 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 179 (accept_3_2 10 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 179 (accept_3_2 7 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 179 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 68 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 179 (accept_3_2 4 68 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  68 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 179 (accept_3_2 1 68 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 179 (allA_of_3_0 67 67 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 179 (allA_succ_of_accept 65 66 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 179 (accept_3_2 64 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 179 (accept_3_2 61 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 66 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 179 (accept_3_2 58 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 179 (accept_3_2 55 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 179 (Polychromatic418967fa.accept_15_9_6_14_1_2627 54 66 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 179 (accept_3_2 52 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 179 (accept_3_2 49 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 66 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 179 (accept_3_2 46 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 179 (Polychromatic418967fa.accept_23_21_20_18_1_10079 44 66 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 179 (accept_3_2 43 66 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 66 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 179 (accept_3_2 40 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 179 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 179 (accept_3_2 37 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 66 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 179
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 179 (accept_3_2 34 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 179 (accept_3_2 31 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 179 (Polychromatic418967fa.accept_13_4_1_10_1_693 30 66 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 179 (accept_3_2 28 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 179 (Polychromatic418967fa.accept_19_7_9_8_1_7297 26 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 179 (accept_3_2 25 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 66 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 179 (accept_3_2 22 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 179 (accept_3_2 19 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 179 (Polychromatic418967fa.accept_17_1_15_9_1_1743 18 66 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 179 (accept_3_2 16 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 179 (accept_3_2 13 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 179 (Polychromatic418967fa.accept_21_12_3_11_1_10078 12 66 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 179 (accept_3_2 10 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 66 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 179 (accept_3_2 7 66 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 66 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 179 (accept_3_2 4 66 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 3
  66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 179 (accept_3_2 1 66 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 179 (allA_succ_of_accept 64 65 179
  (accept_3_2 64 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 179
  (Polychromatic418967fa.accept_17_12_14_9_1_5079 63 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 179 (accept_3_2 61 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 59
  65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 179 (accept_3_2 58 65
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 179 (Polychromatic418967fa.accept_10_6_5_9_1_1233 56 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 179 (accept_3_2 55 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 179 (Polychromatic418967fa.accept_15_8_5_14_1_986
  53 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 179 (accept_3_2 52
  65 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 179
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 179 (accept_3_2 49 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 65 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 47
  65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 179 (accept_3_2 46 65
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 179
  (Polychromatic418967fa.accept_16_13_1_3_1_2205 45 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 65 179 (Polychromatic418967fa.accept_10_4_5_9_1_1231 44 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 179 (accept_3_2 43 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 41
  65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 179 (accept_3_2 40 65
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 179 (accept_3_2 37 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 65 179 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 179
  (Polychromatic418967fa.accept_20_15_5_19_1_5686 35 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 179 (accept_3_2 34 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 179 (accept_3_2 31 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 179
  (Polychromatic418967fa.accept_11_7_10_3_1_633 29 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 179 (accept_3_2 28 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 179 (accept_3_2 25 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 179 (accept_3_2 22 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 179 (accept_3_2 19 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 179
  (Polychromatic418967fa.accept_15_2_5_14_1_61 17 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 179 (accept_3_2 16 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 179 (accept_3_2 13 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 179
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 179 (accept_3_2 10 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 179 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 179 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 179 (accept_3_2 7 65 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 179 (accept_3_2 4 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  179 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 65 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 179 (accept_3_2 1 65 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 179
  (allA_of_3_0 64 64 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 179 (allA_succ_of_accept 62 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 179 (accept_3_2 61 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 179 (Polychromatic418967fa.accept_14_3_7_11_1_765 59 63 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 179 (accept_3_2 58 63 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 179 (accept_3_2 55 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 179 (Polychromatic418967fa.accept_13_1_11_10_1_1258 53 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 179 (accept_3_2 52 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 179 (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 63
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 179 (accept_3_2 49 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 179 (Polychromatic418967fa.accept_17_14_12_9_1_2774 48 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 179 (Polychromatic418967fa.accept_13_8_11_10_1_636 47 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 179 (accept_3_2 46 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 63
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 179 (accept_3_2 43 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 179 (Polychromatic418967fa.accept_13_3_11_10_1_2647 42 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 179 (Polychromatic418967fa.accept_13_2_11_10_1_1881 41 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 179 (accept_3_2 40 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 179 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 63 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 179 (accept_3_2 37 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 179 (Polychromatic418967fa.accept_19_16_6_8_1_8772 35 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 179 (accept_3_2 34 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 179 (accept_3_2 31 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 179 (Polychromatic418967fa.accept_13_4_11_10_1_1226 30 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 179 (Polychromatic418967fa.accept_13_3_11_10_1_2647 29 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 179 (accept_3_2 28 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 179 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 63 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 179 (accept_3_2 25 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 179 (Polychromatic418967fa.accept_16_7_15_3_1_1302 23 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 179 (accept_3_2 22 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 63
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 179 (accept_3_2 19 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 179 (Polychromatic418967fa.accept_14_4_7_11_1_790 18 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 179 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 63 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 179 (accept_3_2 16 63 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 179 (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 179 (accept_3_2 13 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 179 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 179 (accept_3_2 10 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 179 (accept_3_2 7 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  179 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 179 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 63 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 179 (accept_3_2 4 63 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 179 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 63 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 179 (accept_3_2 1 63 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 179 (allA_succ_of_accept 61 62 179
  (accept_3_2 61 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 179
  (Polychromatic418967fa.accept_19_3_5_8_1_8790 60 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 179 (accept_3_2 58 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 179 (Polychromatic418967fa.accept_12_8_2_11_1_246
  56 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 179 (accept_3_2 55
  62 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 179 (accept_3_2 52 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 179 (Polychromatic418967fa.accept_15_5_2_14_1_1693
  50 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 179 (accept_3_2 49
  62 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 179
  (Polychromatic418967fa.accept_11_4_7_3_1_289 48 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 179 (accept_3_2 46 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 179 (accept_3_2 43 62
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 179
  (Polychromatic418967fa.accept_15_12_2_14_1_5659 42 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 179 (accept_3_2 40 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 179 (accept_3_2 37 62
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 179
  (Polychromatic418967fa.accept_17_2_11_9_1_1739 36 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 179 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 179 (accept_3_2 34 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 179 (Polychromatic418967fa.accept_11_10_7_3_1_3679
  32 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 179 (accept_3_2 31
  62 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 62 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 179 (accept_3_2 28 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 62 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 26
  62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 179 (accept_3_2 25 62
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 179 (Polychromatic418967fa.accept_7_3_6_4_1_30
  24 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 179 (accept_3_2 22 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 179 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 62 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 179 (accept_3_2 19 62 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 179 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 62 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 179 (accept_3_2 16 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 179 (Polychromatic418967fa.accept_19_14_5_8_1_10077 14 62 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 179 (accept_3_2 13 62 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 62 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 179
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 179 (accept_3_2 10 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 62 179 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 179 (accept_3_2 7 62 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 62 179 (Polychromatic418967fa.accept_21_6_20_11_1_7067 6 62 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 179 (accept_3_2 4 62 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 62 179 (accept_3_2 1 62 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 179 (allA_of_3_0 61 61 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 179 (allA_succ_of_accept 59 60 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 179 (accept_3_2 58 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 179 (accept_3_2 55 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 179 (Polychromatic418967fa.accept_13_2_8_10_1_1902 54 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 179
  (Polychromatic418967fa.accept_19_15_3_8_1_8789 53 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 179 (accept_3_2 52 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 179 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 179 (accept_3_2 49 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 179
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 179 (accept_3_2 46 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 179 (Polychromatic418967fa.accept_21_3_18_11_1_10061 45 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 179 (Polychromatic418967fa.accept_13_5_8_10_1_4363 44 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 179 (accept_3_2 43 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 179 (Polychromatic418967fa.accept_16_10_12_3_1_4252 42 60
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 179 (accept_3_2 40 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 179 (accept_3_2 37 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 179 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 179
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 35 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 179 (accept_3_2 34 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 179 (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 179 (accept_3_2 31 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 179 (accept_3_2 28 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 179 (Polychromatic418967fa.accept_21_6_18_11_1_3960 27 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 179 (Polychromatic418967fa.accept_16_10_12_3_1_4252 26 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 179 (accept_3_2 25 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 179 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 60
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 179
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 179 (accept_3_2 22 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 179 (accept_3_2 19 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 179 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 179
  (Polychromatic418967fa.accept_13_4_8_10_1_671 17 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 179 (accept_3_2 16 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 179 (accept_3_2 13 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 179 (accept_3_2 10 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 179 (Polychromatic418967fa.accept_16_9_12_3_1_3138 9 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 179 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 179 (accept_3_2 7 60 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 179 (Polychromatic418967fa.accept_19_6_3_8_1_7283 6 60 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 179 (accept_3_2 4 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 60 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 179 (accept_3_2 1 60 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 179
  (allA_succ_of_accept 58 59 179 (accept_3_2 58 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 179 (accept_3_2 55 59 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 179 (Polychromatic418967fa.accept_16_6_11_3_1_2198 54 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 179
  (Polychromatic418967fa.accept_19_15_2_8_1_7263 53 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 179 (accept_3_2 52 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 59 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 179 (accept_3_2 49 59 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 179 (accept_3_2 46 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 179 (Polychromatic418967fa.accept_17_11_8_9_1_8919 45 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 179 (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 179 (accept_3_2 43 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 179
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 179 (accept_3_2 40 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 179 (accept_3_2 37 59 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 179
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 179 (accept_3_2 34 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 179 (Polychromatic418967fa.accept_19_13_2_8_1_4484 32 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 179 (accept_3_2 31 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 59 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 179 (accept_3_2 28 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 179 (Polychromatic418967fa.accept_18_8_5_17_1_1388 26 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 179 (accept_3_2 25 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 179
  (Polychromatic418967fa.accept_16_7_11_3_1_1330 23 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 179 (accept_3_2 22 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 59 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 179 (accept_3_2 19 59 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 179 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 179
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 179 (accept_3_2 16 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 179 (Polychromatic418967fa.accept_16_14_11_3_1_4249 14 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 179 (accept_3_2 13 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 179 (accept_3_2 10 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 179 (Polychromatic418967fa.accept_22_9_15_3_1_8548 9 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 59 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 179 (accept_3_2 7 59 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 59 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 179
  (Polychromatic418967fa.accept_19_5_2_8_1_8803 5 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 179 (accept_3_2 4 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  179 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 59 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 59 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 179 (accept_3_2 1 59 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 179 (allA_of_3_0
  58 58 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 179 (allA_succ_of_accept 56 57 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 179 (accept_3_2 55 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 179 (Polychromatic418967fa.accept_23_7_11_18_1_6779 53 57 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 179 (accept_3_2 52 57 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 57 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 179 (accept_3_2 49 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 179 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 179 (accept_3_2 46 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 179 (accept_3_2 43 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 179 (accept_3_2 40 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 57 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 179 (accept_3_2 37 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 179 (Polychromatic418967fa.accept_20_16_17_19_1_8721 36 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 179 (Polychromatic418967fa.accept_20_15_17_19_1_10076 35 57 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 179 (accept_3_2 34 57 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 179 (accept_3_2 31 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 179 (accept_3_2 28 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 57 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 179 (accept_3_2 25 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 179 (accept_3_2 22 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 179 (Polychromatic418967fa.accept_13_8_5_10_1_2701 21 57 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 179 (accept_3_2 19 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 179 (accept_3_2 16 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 179 (accept_3_2 13 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 179 (accept_3_2 10 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 179 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 57 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 179 (accept_3_2 7 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 179 (accept_3_2 4 57 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 179 (accept_3_2 1 57 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 179 (allA_succ_of_accept 55 56 179 (accept_3_2 55 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 179 (Polychromatic418967fa.accept_19_16_18_8_1_8784 54 56 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 179 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 56 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 179 (accept_3_2 52 56 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 179 (accept_3_2 49 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 179 (Polychromatic418967fa.accept_13_8_4_10_1_4358 47 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 179 (accept_3_2 46 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 179
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 44 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 179 (accept_3_2 43 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 179 (accept_3_2 40 56 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 179 (accept_3_2 37 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 179 (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 179 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 56 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 179 (accept_3_2 34 56 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 179 (accept_3_2 31 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 179 (Polychromatic418967fa.accept_16_13_8_3_1_5374 29 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 179 (accept_3_2 28 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 179 (accept_3_2 25 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 179 (accept_3_2 22 56 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 179
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 20 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 179 (accept_3_2 19 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 179 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 179 (Polychromatic418967fa.accept_20_17_16_19_1_7178 17 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 179 (accept_3_2 16 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 179 (accept_3_2 13 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 179 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 179 (accept_3_2 10 56 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 179
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 8 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 179 (accept_3_2 7 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  179 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 179 (accept_3_2 4 56 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 179 (Polychromatic418967fa.accept_11_2_1_3_1_683 2
  56 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 179 (accept_3_2 1 56 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 179))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 179 (allA_of_3_0 55 55 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 179
  (allA_succ_of_accept 53 54 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 179 (accept_3_2 52 54 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 50
  54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 179 (accept_3_2 49 54
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 179 (Polychromatic418967fa.accept_13_8_2_10_1_652 47 54 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 179 (accept_3_2 46 54 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 44
  54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 179 (accept_3_2 43 54
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 179
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 179 (accept_3_2 40 54 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 179 (Polychromatic418967fa.accept_19_1_16_8_1_10075 39 54 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 179
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 179 (accept_3_2 37 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  54 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 54 179 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 179 (accept_3_2 34 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 179
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 32 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 179 (accept_3_2 31 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  54 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 54 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 179 (accept_3_2 28 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 179
  (Polychromatic418967fa.accept_19_7_16_8_1_8761 26 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 179 (accept_3_2 25 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 179 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 179 (accept_3_2 22 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 179 (accept_3_2 19 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 179 (accept_3_2 16 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 179
  (Polychromatic418967fa.accept_21_14_12_11_1_3956 14 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 54 179 (accept_3_2 13 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 54 179 (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 54 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 179 (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 54
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 179 (accept_3_2 10 54 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 179 (accept_3_2 7 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 179 (accept_3_2 4 54 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 179 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 54 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  54 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 179 (accept_3_2 1 54 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 179))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 179 (allA_succ_of_accept 52 53 179 (accept_3_2 52 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 179 (Polychromatic418967fa.accept_15_6_8_14_1_4575 51 53 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 179 (accept_3_2 49 53 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 179 (Polychromatic418967fa.accept_13_9_1_10_1_647
  48 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 179
  (Polychromatic418967fa.accept_24_23_5_11_1_10074 47 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 53 179 (accept_3_2 46 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 53 179 (Polychromatic418967fa.accept_17_11_2_9_1_6358 45 53 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 53 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 179 (accept_3_2 43 53 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 179
  (Polychromatic418967fa.accept_17_7_2_9_1_6396 41 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 179 (accept_3_2 40 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 179 (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 179 (accept_3_2 37 53 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 179 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 53 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 179
  (Polychromatic418967fa.accept_13_9_1_10_1_647 35 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 179 (accept_3_2 34 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 179 (Polychromatic418967fa.accept_22_11_9_3_1_10073 33 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 179 (Polychromatic418967fa.accept_20_12_13_19_1_8690 32 53 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 179 (accept_3_2 31 53 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 179
  (Polychromatic418967fa.accept_20_9_13_19_1_10072 29 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 53 179 (accept_3_2 28 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 53 179 (Polychromatic418967fa.accept_22_5_9_3_1_5251 27 53 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 179 (accept_3_2 25 53 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262
  24 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 179
  (Polychromatic418967fa.accept_19_4_15_8_1_5937 23 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 179 (accept_3_2 22 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 179 (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 179 (Polychromatic418967fa.accept_15_5_8_14_1_432 20 53 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 179 (accept_3_2 19 53 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 179
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 179 (accept_3_2 16 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 179 (Polychromatic418967fa.accept_22_15_9_3_1_10071 15 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 179 (accept_3_2 13 53 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 179 (Polychromatic418967fa.accept_19_12_15_8_1_10070 12 53 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 179
  (Polychromatic418967fa.accept_13_11_1_10_1_648 11 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 179 (accept_3_2 10 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 179 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 179 (Polychromatic418967fa.accept_16_8_5_3_1_4297 8 53 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 179 (accept_3_2 7 53 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 179
  (Polychromatic418967fa.accept_15_5_8_14_1_432 5 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 179 (accept_3_2 4 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  179 (Polychromatic418967fa.accept_19_3_15_8_1_3232 3 53 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 53 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 179 (accept_3_2 1 53 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 53 179))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 179
  (allA_of_3_0 52 52 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 179 (allA_succ_of_accept 50 51 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 179 (accept_3_2 49 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 179 (accept_3_2 46 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 51 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 179 (accept_3_2 43 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 179 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 179 (accept_3_2 40 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 179 (accept_3_2 37 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 179 (Polychromatic418967fa.accept_21_15_9_11_1_5417 36 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 179 (accept_3_2 34 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 179 (accept_3_2 31 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 179 (accept_3_2 28 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 179 (accept_3_2 25 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 179 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 179 (accept_3_2 22 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 179 (accept_3_2 19 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 179 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 179 (Polychromatic418967fa.accept_23_17_5_18_1_10069 17 51 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 179 (accept_3_2 16 51 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 51 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 179 (accept_3_2 13 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 179 (accept_3_2 10 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 51 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 179 (accept_3_2 7 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 51 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 179 (accept_3_2 4 51 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 51 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 179 (accept_3_2 1 51 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 179)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 179 (allA_succ_of_accept 49 50 179 (accept_3_2 49 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 50 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 50 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 179 (accept_3_2 46 50 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 179 (accept_3_2 43 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 179 (accept_3_2 40 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 179
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 179 (accept_3_2 37 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 179 (Polychromatic418967fa.accept_15_6_5_14_1_429 36 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 179 (Polychromatic418967fa.accept_20_15_10_19_1_10068 35 50 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 179 (accept_3_2 34 50 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 179
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 179 (accept_3_2 31 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 179 (accept_3_2 28 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 179 (accept_3_2 25 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 179 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 179 (accept_3_2 22 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 179 (accept_3_2 19 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 179 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 179 (accept_3_2 16 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 50 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 179
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 179 (accept_3_2 13 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 179 (accept_3_2 10 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 179
  (Polychromatic418967fa.accept_11_8_6_3_1_661 8 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 179 (accept_3_2 7 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  179 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 50 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 179 (accept_3_2 4 50 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 50
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 179 (accept_3_2 1 50 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 179)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 179 (allA_of_3_0 49 49 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 179 (allA_succ_of_accept 47 48
  179 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 179 (accept_3_2 46 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 179 (accept_3_2 43 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 48 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 179 (accept_3_2 40 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 179 (Polychromatic418967fa.accept_17_5_14_9_1_5104 39 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 179 (accept_3_2 37 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 179 (Polychromatic418967fa.accept_19_17_10_8_1_5942 36 48 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 179
  (Polychromatic418967fa.accept_19_16_10_8_1_10067 35 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 48 179 (accept_3_2 34 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 48 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 179 (accept_3_2 31 48 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 30
  48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 179 (accept_3_2 28 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 179 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 179 (accept_3_2 25 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 48 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 179
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 179 (accept_3_2 22 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 179 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 179 (accept_3_2 19 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 179 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 48 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 179
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 179 (accept_3_2 16 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 179 (accept_3_2 13 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 48 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 179 (accept_3_2 10 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 179 (Polychromatic418967fa.accept_25_8_23_4_1_10066 8 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 179 (accept_3_2 7 48 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 48 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 179 (accept_3_2 4 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 48 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 179 (accept_3_2 1 48 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 179)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 179 (allA_succ_of_accept 46
  47 179 (accept_3_2 46 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 179
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 45 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 179 (accept_3_2 43 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 41
  47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 179 (accept_3_2 40 47
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 179 (Polychromatic418967fa.accept_10_8_7_9_1_425 38 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 179 (accept_3_2 37 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 179 (Polychromatic418967fa.accept_15_5_2_14_1_1693
  35 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 179 (accept_3_2 34
  47 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 179
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 179 (accept_3_2 31 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 47 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 179 (accept_3_2 28 47
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 179
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 179 (Polychromatic418967fa.accept_19_7_9_8_1_7297 26 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 179 (accept_3_2 25 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 23
  47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 179 (accept_3_2 22 47
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 179
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 179 (accept_3_2 19 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 179 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 47 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 179 (Polychromatic418967fa.accept_13_4_8_10_1_671
  17 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 179 (accept_3_2 16
  47 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 179
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 179 (accept_3_2 13 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 179 (Polychromatic418967fa.accept_13_11_8_10_1_676
  11 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 179 (accept_3_2 10
  47 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 179 (accept_3_2 7 47 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 47 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 179 (accept_3_2 4 47 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 179 (accept_3_2 1 47 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  179))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 179 (allA_of_3_0 46 46 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 179 (allA_succ_of_accept 44 45 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 179 (accept_3_2 43 45 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 179
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 179 (accept_3_2 40 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  45 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 45 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 179 (accept_3_2 37 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 179
  (Polychromatic418967fa.accept_11_2_1_3_1_683 35 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 179 (accept_3_2 34 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  45 179 (Polychromatic418967fa.accept_16_1_13_3_1_2168 33 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 45 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 179 (accept_3_2 31 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 179 (accept_3_2 28 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  45 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 45 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 179 (accept_3_2 25 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 179 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 45 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 179
  (Polychromatic418967fa.accept_25_23_20_4_1_10065 23 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 45 179 (accept_3_2 22 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 45 179 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 45 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 179 (accept_3_2 19 45 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 179
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 179 (accept_3_2 16 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  45 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 45 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 179 (accept_3_2 13 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 179 (Polychromatic418967fa.accept_13_12_6_10_1_667 12 45 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 179
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 179 (accept_3_2 10 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  45 179 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 45 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 179 (accept_3_2 7 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 179
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 179 (accept_3_2 4 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45
  179 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 45 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 45 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 179 (accept_3_2 1 45 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 45 179))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 179
  (allA_succ_of_accept 43 44 179 (accept_3_2 43 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  44 179 (Polychromatic418967fa.accept_16_10_12_3_1_4252 42 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 44 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 179 (accept_3_2 40 44 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 179
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 179 (accept_3_2 37 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 179 (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 179 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 44 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 179 (accept_3_2 34 44 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 179
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 32 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 179 (accept_3_2 31 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 179 (Polychromatic418967fa.accept_13_4_5_10_1_1247 30 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 179 (Polychromatic418967fa.accept_20_9_4_19_1_10052 29 44 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 179 (accept_3_2 28 44 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 179 (accept_3_2 25 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 179 (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 44 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 179 (accept_3_2 22 44 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 179
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 179 (accept_3_2 19 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 179 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 44 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 179 (accept_3_2 16 44 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 179 (accept_3_2 13 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 179 (Polychromatic418967fa.accept_25_11_19_4_1_10064 11 44 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 179 (accept_3_2 10 44 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 179
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 179 (accept_3_2 7 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 44 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 179 (accept_3_2 4 44 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 179 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  44 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 179 (accept_3_2 1 44 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 179)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  179 (allA_of_3_0 43 43 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 179 (allA_succ_of_accept 41 42 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 179 (accept_3_2 40 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 42 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 179 (accept_3_2 37 42 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 179 (Polychromatic418967fa.accept_19_17_4_8_1_4500 36 42 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 179
  (Polychromatic418967fa.accept_17_1_8_9_1_1810 35 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 179 (accept_3_2 34 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 42 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 179 (accept_3_2 31 42 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 42 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 179 (accept_3_2 28 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 179 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 179 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 42 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 179 (accept_3_2 25 42 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 179 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 42
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 179 (accept_3_2 22 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 42 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 179 (accept_3_2 19 42 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 179 (Polychromatic418967fa.accept_17_1_8_9_1_1810 18 42 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 179 (accept_3_2 16 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 179 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 42 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 179 (accept_3_2 13 42 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 42 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 179 (accept_3_2 10 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 179 (Polychromatic418967fa.accept_22_8_20_3_1_10063 8 42 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 179 (accept_3_2 7 42 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 42 179 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 42 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 179 (accept_3_2 4 42 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 179
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 179 (accept_3_2 1 42 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  179)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 179 (allA_succ_of_accept 40 41 179 (accept_3_2 40 41 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 39
  41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 179 (accept_3_2 37 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 179 (Polychromatic418967fa.accept_17_2_7_9_1_2796 36 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 179 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 179 (accept_3_2 34 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 41 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 179
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 179 (accept_3_2 31 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 179 (accept_3_2 28 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 179 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 41 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 179 (accept_3_2 25 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 179 (accept_3_2 22 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 41 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 179 (accept_3_2 19 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 179 (accept_3_2 16 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 41 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 179 (accept_3_2 13 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 179 (accept_3_2 10 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 179
  (Polychromatic418967fa.accept_10_8_1_9_1_413 8 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 179 (accept_3_2 7 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 179 (accept_3_2 4 41 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 41 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 179 (accept_3_2 1 41 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 179))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 179
  (allA_of_3_0 40 40 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 179 (allA_succ_of_accept 38 39 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 179 (accept_3_2 37 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 179 (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 39 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 179 (accept_3_2 34 39 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 39 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 179 (accept_3_2 31 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 179 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 39 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 179 (accept_3_2 28 39 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 179 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 39 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 179 (accept_3_2 25 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 39 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 179 (accept_3_2 22 39 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 39 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 179 (accept_3_2 19 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 179 (Polychromatic418967fa.accept_19_18_1_8_1_7291 18 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 179 (Polychromatic418967fa.accept_23_17_16_18_1_10062 17 39 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 179 (accept_3_2 16 39 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 179 (accept_3_2 13 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 179 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 179 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 39 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 179 (accept_3_2 10 39 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 179 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 39 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 179 (accept_3_2 7 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  179 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 39 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 179 (accept_3_2 4 39 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 179 (Polychromatic418967fa.accept_21_3_18_11_1_10061 3 39 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 179 (accept_3_2 1 39 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  179))))))))))))))))))))))))))))))))))))))) (allB_succ 38 179 (allA_succ_of_accept 37 38 179 (accept_3_2 37 38 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 38 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 36
  38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 38 179
  (Polychromatic418967fa.accept_13_9_12_10_1_242 35 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 38 179 (accept_3_2 34 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  38 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 38 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 38 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 38 179 (accept_3_2 31 38 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 38 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 38 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 38 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 38 179 (accept_3_2 28 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  38 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 38 179 (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 38 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 38 179 (accept_3_2 25 38 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 38 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 38 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 38 179
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 38 179 (accept_3_2 22 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  38 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 38 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 38 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 38 179 (accept_3_2 19 38 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 38 179 (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 38 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 38 179 (accept_3_2 16 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  38 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 38 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 38 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 38 179 (accept_3_2 13 38 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 38 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 38 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 38 179
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 38 179 (accept_3_2 10 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  38 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 38 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 38 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 38 179 (accept_3_2 7 38 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 38 179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 38 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 38 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 179 (accept_3_2 4 38 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 38 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 179
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 2 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 38 179 (accept_3_2 1 38 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  179)))))))))))))))))))))))))))))))))))))) (allB_succ 37 179 (allA_of_3_0 37 37 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 36 179 (allA_succ_of_accept 35 36 179 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 36 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 179 (accept_3_2 34 36 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 33
  36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 179
  (Polychromatic418967fa.accept_14_4_8_11_1_794 32 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 179 (accept_3_2 31 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  36 179 (Polychromatic418967fa.accept_19_11_17_8_1_7259 30 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 36 179 (Polychromatic418967fa.accept_19_10_17_8_1_5917 29 36 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 179 (accept_3_2 28 36 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 179 (Polychromatic418967fa.accept_21_6_15_11_1_5410 27 36
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 179
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 179 (accept_3_2 25 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  36 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 36 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 36 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 179 (accept_3_2 22 36 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 179 (Polychromatic418967fa.accept_17_4_2_9_1_3896 21 36 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 179
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 179 (accept_3_2 19 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  36 179 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 36 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 179 (accept_3_2 16 36 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 179 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 179
  (Polychromatic418967fa.accept_25_14_11_4_1_10060 14 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 36 179 (accept_3_2 13 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 36 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 36 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 179 (Polychromatic418967fa.accept_17_11_2_9_1_6358 11 36
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 179 (accept_3_2 10 36 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 36 179 (Polychromatic418967fa.accept_15_9_6_14_1_2627
  9 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 179
  (Polychromatic418967fa.accept_15_8_6_14_1_975 8 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 179 (accept_3_2 7 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36
  179 (Polychromatic418967fa.accept_16_6_4_3_1_2189 6 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 36 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 179 (accept_3_2 4 36 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 179
  (Polychromatic418967fa.accept_22_2_14_3_1_10059 2 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 36 179 (accept_3_2 1 36 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  179)))))))))))))))))))))))))))))))))))) (allB_succ 35 179 (allA_succ_of_accept 34 35 179 (accept_3_2 34 35 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 179
  (Polychromatic418967fa.accept_21_12_14_11_1_3921 33 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 179 (Polychromatic418967fa.accept_13_6_9_10_1_1201 32 35 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 179 (accept_3_2 31 35 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 179 (Polychromatic418967fa.accept_19_11_16_8_1_2098 30 35
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 179
  (Polychromatic418967fa.accept_19_10_16_8_1_3289 29 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 179 (accept_3_2 28 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 179 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 179 (Polychromatic418967fa.accept_10_6_5_9_1_1233 26 35 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 179 (accept_3_2 25 35 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 179 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 35 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 179
  (Polychromatic418967fa.accept_11_1_2_3_1_688 23 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 179 (accept_3_2 22 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 179 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 179 (Polychromatic418967fa.accept_17_3_1_9_1_9012 20 35 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 179 (accept_3_2 19 35 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 179 (Polychromatic418967fa.accept_14_4_7_11_1_790 18 35 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 179
  (Polychromatic418967fa.accept_14_3_7_11_1_765 17 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 179 (accept_3_2 16 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 179 (Polychromatic418967fa.accept_17_15_1_9_1_10058 15 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 179 (Polychromatic418967fa.accept_10_4_5_9_1_1231 14 35 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 179 (accept_3_2 13 35 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 179 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 35 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 179
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 179 (accept_3_2 10 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 179 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 179 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 35 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 179 (accept_3_2 7 35 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 179 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 35 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 179
  (Polychromatic418967fa.accept_19_5_16_8_1_10057 5 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 179 (accept_3_2 4 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  179 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 35 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 35 179 (Polychromatic418967fa.accept_15_2_5_14_1_61 2 35 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 179 (accept_3_2 1 35 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 35 179))))))))))))))))))))))))))))))))))) (allB_succ 34 179 (allA_of_3_0 34 34 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 179 (allA_succ_of_accept 32 33 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 179 (accept_3_2 31 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 33 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 179 (accept_3_2 28 33 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 179 (accept_3_2 25 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 33 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 179 (accept_3_2 22 33 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 179 (accept_3_2 19 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 179 (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 33 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 179 (accept_3_2 16 33 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 179 (accept_3_2 13 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 33 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 179 (accept_3_2 10 33 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 179 (accept_3_2 7 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 33 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 179 (accept_3_2 4 33 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 179 (accept_3_2 1 33 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 179))))))))))))))))))))))))))))))))) (allB_succ 32 179
  (allA_succ_of_accept 31 32 179 (accept_3_2 31 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  32 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 179 (accept_3_2 28 32 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 179 (accept_3_2 25 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 179 (Polychromatic418967fa.accept_17_6_15_9_1_1791 23 32 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 179 (accept_3_2 22 32 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 179 (accept_3_2 19 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 179 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 179 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 32 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 179 (accept_3_2 16 32 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 179 (accept_3_2 13 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 179 (accept_3_2 10 32 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 179
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 179 (accept_3_2 7 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  179 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 32 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 179 (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 32 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 179 (accept_3_2 4 32 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 32
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 179 (accept_3_2 1 32 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 179)))))))))))))))))))))))))))))))) (allB_succ 31 179
  (allA_of_3_0 31 31 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 179 (allA_succ_of_accept 29 30 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 179 (accept_3_2 28 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 30 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 179 (accept_3_2 25 30 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 30 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 179 (accept_3_2 22 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 30 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 179 (accept_3_2 19 30 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 179 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 30 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 179 (accept_3_2 16 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 179 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 30 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 179 (accept_3_2 13 30 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 30 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 179 (accept_3_2 10 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 179 (Polychromatic418967fa.accept_13_8_4_10_1_4358 8 30 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 179 (accept_3_2 7 30 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 30 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 30 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 179 (accept_3_2 4 30 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 179 (Polychromatic418967fa.accept_19_3_11_8_1_3193
  3 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 179 (accept_3_2 1 30 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  179)))))))))))))))))))))))))))))) (allB_succ 29 179 (allA_succ_of_accept 28 29 179 (accept_3_2 28 29 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 179 (Polychromatic418967fa.accept_26_1_3_23_1_10056 27 29
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 179 (accept_3_2 25 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 29 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 179 (accept_3_2 22 29 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 29 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 179
  (Polychromatic418967fa.accept_13_7_3_10_1_656 20 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 179 (accept_3_2 19 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 179 (accept_3_2 16 29 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 29 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 179 (accept_3_2 13 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 179 (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 29 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 179 (accept_3_2 10 29 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 179 (Polychromatic418967fa.accept_23_9_6_18_1_10055 9 29 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 179
  (Polychromatic418967fa.accept_16_8_13_3_1_4253 8 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 179 (accept_3_2 7 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 179 (accept_3_2 4 29 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 29 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 179 (accept_3_2 1 29 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 179))))))))))))))))))))))))))))) (allB_succ 28 179 (allA_of_3_0
  28 28 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 179 (allA_succ_of_accept 26 27 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 179 (accept_3_2 25 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 27 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 179 (accept_3_2 22 27 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 179 (accept_3_2 19 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 179 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 27 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 179 (accept_3_2 16 27 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 179 (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 27 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 179 (accept_3_2 13 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 179 (Polychromatic418967fa.accept_13_11_1_10_1_648 11 27 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 179 (accept_3_2 10 27 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 179 (accept_3_2 7 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  179 (Polychromatic418967fa.accept_16_6_11_3_1_2198 6 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 27 179 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 27 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 179 (accept_3_2 4 27 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 179 (accept_3_2 1 27 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  179))))))))))))))))))))))))))) (allB_succ 26 179 (allA_succ_of_accept 25 26 179 (accept_3_2 25 26 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 179 (Polychromatic418967fa.accept_27_24_26_17_1_10054 24 26
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 179 (accept_3_2 22 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 26 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 179 (accept_3_2 19 26 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 179 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 26 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 179
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 179 (accept_3_2 16 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 179 (Polychromatic418967fa.accept_19_14_7_8_1_10053 14 26 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 179 (accept_3_2 13 26 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 179 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12 26
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 179
  (Polychromatic418967fa.accept_19_11_7_8_1_2110 11 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 179 (accept_3_2 10 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 26 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 179 (accept_3_2 7 26 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 26 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 179 (accept_3_2 4 26 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 179
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 179 (accept_3_2 1 26 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  179)))))))))))))))))))))))))) (allB_succ 25 179 (allA_of_3_0 25 25 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 179 (allA_succ_of_accept 23 24 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 24 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 179 (accept_3_2 22 24 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 179
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 24 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 179 (accept_3_2 19 24 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 179 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 24 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 179 (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 24 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 179 (accept_3_2 16 24 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 179
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 24 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 179 (accept_3_2 13 24 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 24 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 179 (accept_3_2 10 24 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 179 (Polychromatic418967fa.accept_20_9_4_19_1_10052 9 24 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 24 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 179 (accept_3_2 7 24 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  179 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 24 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 179 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 179 (accept_3_2 4 24 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 24 179 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  24 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 179 (accept_3_2 1 24 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 179)))))))))))))))))))))))) (allB_succ 23 179
  (allA_succ_of_accept 22 23 179 (accept_3_2 22 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  23 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 23 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 179 (accept_3_2 19 23 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 179 (Polychromatic418967fa.accept_19_18_4_8_1_3282 18 23 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 179
  (Polychromatic418967fa.accept_19_17_4_8_1_4500 17 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 179 (accept_3_2 16 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 179 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 179 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 23 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 179 (accept_3_2 13 23 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 179
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 179 (accept_3_2 10 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 179 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 179 (Polychromatic418967fa.accept_17_8_6_9_1_7768 8 23 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 179 (accept_3_2 7 23 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 179 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 23 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 179
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 179 (accept_3_2 4 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  179 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 23 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 179 (accept_3_2 1 23 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 179))))))))))))))))))))))) (allB_succ 22 179 (allA_of_3_0 22 22 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 179 (allA_succ_of_accept 20 21 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 179 (accept_3_2 19 21 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  21 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 179
  (Polychromatic418967fa.accept_13_4_8_10_1_671 17 21 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 179 (accept_3_2 16 21 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 179 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 179 (accept_3_2 13 21 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 179 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 21 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 21 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 179 (accept_3_2 10 21 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 179 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 21 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 179 (accept_3_2 7 21 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 21 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 179 (accept_3_2 4 21 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  179 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 179 (accept_3_2 1 21 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 179))))))))))))))))))))) (allB_succ 20 179 (allA_succ_of_accept 19 20 179
  (accept_3_2 19 20 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 179
  (Polychromatic418967fa.accept_17_1_3_9_1_958 18 20 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 179 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 20 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 179 (accept_3_2 16 20 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  20 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 179 (accept_3_2 13 20
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 20 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 179 (Polychromatic418967fa.accept_17_11_3_9_1_6387 11 20 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 179 (accept_3_2 10 20 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 179 (Polychromatic418967fa.accept_13_8_7_10_1_4362
  8 20 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 179 (accept_3_2 7 20
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 179 (Polychromatic418967fa.accept_9_6_2_8_1_592
  6 20 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 179
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 20 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 179 (accept_3_2 4 20 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 20 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 179 (accept_3_2 1 20 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 179)))))))))))))))))))) (allB_succ 19 179 (allA_of_3_0 19 19 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 179 (allA_succ_of_accept 17 18 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 179 (accept_3_2 16 18 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 179 (Polychromatic418967fa.accept_11_4_7_3_1_289
  15 18 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 179
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 18 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 179 (accept_3_2 13 18 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 179 (Polychromatic418967fa.accept_21_12_18_11_1_10051 12 18 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 179 (Polychromatic418967fa.accept_10_1_8_9_1_787 11 18 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 179 (accept_3_2 10 18 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 179
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 8 18 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 179 (accept_3_2 7 18 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  179 (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 18 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 18 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 179 (accept_3_2 4 18 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 179 (Polychromatic418967fa.accept_17_3_1_9_1_9012 3 18 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 179
  (Polychromatic418967fa.accept_13_2_5_10_1_250 2 18 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 18 179 (accept_3_2 1 18 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  179)))))))))))))))))) (allB_succ 17 179 (allA_succ_of_accept 16 17 179 (accept_3_2 16 17 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 179 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 17 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 179 (accept_3_2 13 17 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 179 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 17 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 179 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 17 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 179 (accept_3_2 10 17 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 179 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 17 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 179
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 17 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 179 (accept_3_2 7 17 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 179 (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 17 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 179 (accept_3_2 4 17 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 179 (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 17 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 179 (accept_3_2 1 17 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 179))))))))))))))))) (allB_succ 16 179 (allA_of_3_0 16 16 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 179 (allA_succ_of_accept 14 15 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 179 (accept_3_2 13 15 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 179 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 15 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 179 (accept_3_2 10 15 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 179 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 15 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 179 (accept_3_2 7 15 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  179 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 15 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 15 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 15 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 179 (accept_3_2 4 15 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 179 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 179
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 179 (accept_3_2 1 15 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  179))))))))))))))) (allB_succ 14 179 (allA_succ_of_accept 13 14 179 (accept_3_2 13 14 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 14 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 11
  14 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 179 (accept_3_2 10 14
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  14 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 179
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 14 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 14 179 (accept_3_2 7 14 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14
  179 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 14 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 179 (accept_3_2 4 14 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 179 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 14
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 179 (accept_3_2 1 14 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 179)))))))))))))) (allB_succ 13 179 (allA_of_3_0 13 13 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 179 (allA_succ_of_accept 11 12 179
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 12 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 179 (accept_3_2 10 12 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  12 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 12 179 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 12 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 179 (accept_3_2 7 12 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 179 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 12 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 179
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 179 (accept_3_2 4 12 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  179 (Polychromatic418967fa.accept_21_3_12_11_1_7034 3 12 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 12 179 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 12 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 179 (accept_3_2 1 12 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 12 179)))))))))))) (allB_succ 11 179 (allA_succ_of_accept 10 11 179 (accept_3_2 10 11
  179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 179
  (Polychromatic418967fa.accept_19_9_11_8_1_10050 9 11 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 179 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 11 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 179 (accept_3_2 7 11 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 179 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 11 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 179 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  11 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 179 (accept_3_2 4 11 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 179 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  11 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 179
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 11 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 179 (accept_3_2 1 11 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  179))))))))))) (allB_succ 10 179 (allA_of_3_0 10 10 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 179
  (allA_succ_of_accept 8 9 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 179 (accept_3_2 7 9 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 179 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 179 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 179 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9
  179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 179 (accept_3_2 4 9 179
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 179 (Polychromatic418967fa.accept_12_3_9_11_1_231 3
  9 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 179 (accept_3_2 1 9 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 179)))))))))
  (allB_succ 8 179 (allA_succ_of_accept 7 8 179 (accept_3_2 7 8 179 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 179 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 8 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 179 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 8 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 179 (accept_3_2 4 8 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 179 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 179
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 8 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 179 (accept_3_2 1 8 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 179))))))))
  (allB_succ 7 179 (allA_of_3_0 7 7 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 179 (allA_succ_of_accept 5
  6 179 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 179 (accept_3_2 4 6 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 179
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 179 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 6 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 179 (accept_3_2 1 6 179 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 179)))))) (allB_succ 5 179 (allA_succ_of_accept 4 5 179 (accept_3_2 4 5 179 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 179 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 5 179
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 179
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 179 (accept_3_2 1 5 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 179)))))
  (allB_succ 4 179 (allA_of_3_0 4 4 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 179 (allA_succ_of_accept 2
  3 179 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 179 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 179 (accept_3_2 1 3 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 179)))
  (allB_succ 2 179 (allA_succ_of_accept 1 2 179 (accept_3_2 1 2 179 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  179)) (allB_two
  179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


