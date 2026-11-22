-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch185
-- name    : Polychromatic418967fa_Branch185
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:19:39.904213+00:00
-- url     : https://prove2.me/theorems/d9918090-d320-43a7-bb95-50ab41efd81d
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch185_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_185 : allB 185 185 :=
  allB_succ' 2 184 185 (Eq.refl Bool.true) (allA_of_3_0 2 184 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  183 185 (Eq.refl Bool.true) (allA_succ_of_accept 2 183 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 183 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 185 (accept_3_2 1 183 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183 185))) (allB_succ' 4 182 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 182 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 182 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 185 (Polychromatic418967fa.accept_16_2_6_9_1_3473 2 182 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 182 185 (accept_3_2 1 182 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 185)))) (allB_succ' 5 181 185 (Eq.refl Bool.true) (allA_of_3_0
  5 181 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 180 185 (Eq.refl Bool.true) (allA_succ_of_gcd 5 180
  185 5 1 36 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4
  180 185 (accept_3_2 4 180 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 185
  (Polychromatic418967fa.accept_19_3_9_14_1_3595 3 180 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 180 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 180 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 185 (accept_3_2 1 180 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 180 185)))))) (allB_succ' 7 179 185 (Eq.refl Bool.true) (allA_succ_of_accept 6 179 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 179 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 179 185 (Polychromatic418967fa.accept_19_5_8_14_1_6384 5 179 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 185 (accept_3_2 4 179 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 179 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 179 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2
  179 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 185 (accept_3_2 1 179
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179 185))))))) (allB_succ' 8 178 185 (Eq.refl Bool.true)
  (allA_of_3_0 8 178 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 177 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 177 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 177 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 185 (accept_3_2 7 177 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 177 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 177 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 5
  177 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 185 (accept_3_2 4 177
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 185 (Polychromatic418967fa.accept_9_3_6_5_1_63
  3 177 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 177 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 185 (accept_3_2 1 177 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  185))))))))) (allB_succ' 10 176 185 (Eq.refl Bool.true) (allA_succ_of_accept 9 176 185
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 176 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 176 185 (Polychromatic418967fa.accept_13_8_7_3_1_430 8 176 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 176 185 (accept_3_2 7 176 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 176 185 (Polychromatic418967fa.accept_15_6_11_5_1_168 6 176 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 176 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  176 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 185 (accept_3_2 4 176
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 185 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 176 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 176 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 185 (accept_3_2 1 176 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  185)))))))))) (allB_succ' 11 175 185 (Eq.refl Bool.true) (allA_of_3_0 11 175 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 174 185 (Eq.refl Bool.true) (allA_succ_of_accept 11 174 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 174 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 174 185 (accept_3_2 10 174 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  174 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 174 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 174 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 174 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 185 (accept_3_2 7 174 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 174 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 185
  (Polychromatic418967fa.accept_16_5_14_9_1_2572 5 174 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 174 185 (accept_3_2 4 174 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  174 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 174 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 174 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 174 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 185 (accept_3_2 1 174 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 174 185)))))))))))) (allB_succ' 13 173 185 (Eq.refl Bool.true) (allA_succ_of_accept 12
  173 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 173 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 185 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 173 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 185 (accept_3_2 10 173 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 173 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 173 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 185 (accept_3_2 7 173 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 173 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 185 (Polychromatic418967fa.accept_16_5_13_9_1_2594 5 173 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 185 (accept_3_2 4 173 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 173 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 173 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 185 (accept_3_2 1 173 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  185))))))))))))) (allB_succ' 14 172 185 (Eq.refl Bool.true) (allA_of_3_0 14 172 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 171 185 (Eq.refl Bool.true) (allA_succ_of_accept 14 171 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 171 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 185 (accept_3_2 13 171 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 171 185 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 171 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 171 185 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 171 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 185 (accept_3_2 10 171 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 185 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 171 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 185 (accept_3_2 7 171 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  171 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 171 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 171 185 (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 171 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 185 (accept_3_2 4 171 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 185 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 171 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 171 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 185 (accept_3_2 1 171 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  185))))))))))))))) (allB_succ' 16 170 185 (Eq.refl Bool.true) (allA_succ_of_gcd 15 170 185 5 3 34 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 170 185
  (Polychromatic418967fa.accept_18_14_8_5_1_860 14 170 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 170 185 (accept_3_2 13 170 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 170 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 170 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 170 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 170 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 185 5 2 34 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 185
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 170 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 170 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 170 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 185 (accept_3_2 7 170 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 170 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 170 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 170 185 5 1 34 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 170 185 (accept_3_2 4 170 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 170 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 170 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 185 (accept_3_2 1 170 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  185)))))))))))))))) (allB_succ' 17 169 185 (Eq.refl Bool.true) (allA_of_3_0 17 169 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 168 185 (Eq.refl Bool.true) (allA_succ_of_accept 17 168 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 168 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 185 (accept_3_2 16 168 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 168 185 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 168 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 168 185 (Polychromatic418967fa.accept_20_14_8_5_1_6090 14 168 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 185 (accept_3_2 13 168 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 168 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 168 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 168 185 (accept_3_2 10 168 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  168 185 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 168 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 168 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 168 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 185 (accept_3_2 7 168 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 168 185 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 168 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 185
  (Polychromatic418967fa.accept_19_5_16_14_1_2374 5 168 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 185 (accept_3_2 4 168 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  168 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 168 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 168 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 168 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 185 (accept_3_2 1 168 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 168 185)))))))))))))))))) (allB_succ' 19 167 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 167 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 167 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 185 (Polychromatic418967fa.accept_19_17_15_14_1_3623 17
  167 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 185 (accept_3_2 16
  167 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 185
  (Polychromatic418967fa.accept_11_4_2_9_1_496 15 167 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 167 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 167 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 185 (accept_3_2 13 167 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 167 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 167 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 167 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 185 (accept_3_2 10 167 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 167 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 185 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 167 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 185 (accept_3_2 7 167 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 167 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 185
  (Polychromatic418967fa.accept_13_5_11_3_1_902 5 167 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 185 (accept_3_2 4 167 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 167 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 167 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 185 (accept_3_2 1 167 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 185))))))))))))))))))) (allB_succ' 20 166 185 (Eq.refl Bool.true) (allA_of_3_0 20
  166 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 165 185 (Eq.refl Bool.true) (allA_succ_of_gcd 20 165
  185 5 4 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  165 185 (accept_3_2 19 165 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 185
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 165 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 165 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 185 (accept_3_2 16 165 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 165 185 5 3 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 165 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 165 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 185 (accept_3_2 13 165 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 165 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 165 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 165 185 5 2 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 165 185 (Polychromatic418967fa.accept_21_9_18_17_1_7454 9 165 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 185 (accept_3_2 7 165 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  165 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 165 185 5 1 33 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 185 (accept_3_2 4
  165 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 185
  (Polychromatic418967fa.accept_12_3_9_5_1_853 3 165 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 165 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 165 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 185 (accept_3_2 1 165 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 165 185))))))))))))))))))))) (allB_succ' 22 164 185 (Eq.refl Bool.true) (allA_succ_of_accept 21
  164 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 164 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 164 185 (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 164 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 164 185 (accept_3_2 19 164 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 164 185 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 164
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 164 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 164 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 164 185 (accept_3_2 16 164 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 164 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 164 185 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 164 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 164 185 (accept_3_2 13 164 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 164 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 164 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 185
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 164 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 164 185 (accept_3_2 10 164 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  164 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 164 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 164 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 185 (accept_3_2 7 164 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 164 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 164 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 185
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 164 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 164 185 (accept_3_2 4 164 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  164 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 164 185 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 164 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 185 (accept_3_2 1 164 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 185)))))))))))))))))))))) (allB_succ' 23 163 185 (Eq.refl Bool.true) (allA_of_3_0
  23 163 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 162 185 (Eq.refl Bool.true) (allA_succ_of_accept 23
  162 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 162 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 162 185 (accept_3_2 22 162 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 162 185 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 162 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 185 (Polychromatic418967fa.accept_19_1_10_14_1_3597 20 162
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 185 (accept_3_2 19 162
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 162 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 162 185 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 162 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 185 (accept_3_2 16 162 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 162 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 162 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 185 (Polychromatic418967fa.accept_13_1_6_3_1_1547
  14 162 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 185 (accept_3_2 13
  162 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 162 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 162 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 162 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 185 (accept_3_2 10 162 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 162 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 162 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 185 (Polychromatic418967fa.accept_10_8_2_5_1_596 8
  162 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 185 (accept_3_2 7 162
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 185
  (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 162 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 162 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 185 (accept_3_2 4 162 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  162 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 185 (accept_3_2 1 162
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 185)))))))))))))))))))))))) (allB_succ' 25 161 185 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 161 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 161 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 185 (Polychromatic418967fa.accept_15_8_11_5_1_169
  23 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 185 (accept_3_2 22
  161 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 185
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 161 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 161 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 185 (accept_3_2 19 161 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 161 185 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 161 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 185
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 185 (accept_3_2 16 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 161 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 185 (accept_3_2 13 161 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 161 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 185 (accept_3_2 10 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 185 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 185 (Polychromatic418967fa.accept_13_8_5_3_1_427 8 161 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 185 (accept_3_2 7 161 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 161 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 185
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 185 (accept_3_2 4 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 161 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 161 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 185 (accept_3_2 1 161 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 185))))))))))))))))))))))))) (allB_succ' 26 160 185 (Eq.refl Bool.true)
  (allA_of_3_0 26 160 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 159 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 159 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 159 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 185 (accept_3_2 25 159 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 159 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 159 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  159 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 185 (accept_3_2 22
  159 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 185
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 159 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 159 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 185 (accept_3_2 19 159 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 159 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 185 (Polychromatic418967fa.accept_9_8_6_5_1_513
  17 159 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 185 (accept_3_2 16
  159 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 185
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 159 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 159 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 159 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 185 (accept_3_2 13 159 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 159 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 159 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 185 (Polychromatic418967fa.accept_9_2_6_5_1_227
  11 159 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 185 (accept_3_2 10
  159 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 159 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 185 (accept_3_2 7 159 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 185
  (Polychromatic418967fa.accept_21_5_12_17_1_10634 5 159 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 159 185 (accept_3_2 4 159 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 159 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 159 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 185 (accept_3_2 1 159 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 185))))))))))))))))))))))))))) (allB_succ' 28 158 185 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 158 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 158 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 185
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 158 185 (accept_3_2 25 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 158 185 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 158 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 158 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 185 (accept_3_2 22 158 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 158 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 158 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 185
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 158 185 (accept_3_2 19 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 158 185 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 158 185 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 158 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 185 (accept_3_2 16 158 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 158 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 158 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 185
  (Polychromatic418967fa.accept_13_1_2_3_1_911 14 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 158 185 (accept_3_2 13 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 158 185 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 158 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 158 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 185 (accept_3_2 10 158 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 158 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 185 (accept_3_2 7 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 185 (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 158 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 185 (accept_3_2 4 158 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 185
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 185 (accept_3_2 1 158 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  185)))))))))))))))))))))))))))) (allB_succ' 29 157 185 (Eq.refl Bool.true) (allA_of_3_0 29 157 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 156 185 (Eq.refl Bool.true) (allA_succ_of_accept 29 156 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 156 185 (accept_3_2 28 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 156 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 156 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 156 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 185 (accept_3_2 25 156 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 156 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 156 185
  (Polychromatic418967fa.accept_21_2_9_17_1_4376 23 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 156 185 (accept_3_2 22 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 156 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 156 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 156 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 185 (accept_3_2 19 156 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 185 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 156 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 156 185
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 156 185 (accept_3_2 16 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 156 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 156 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 156 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 185 (accept_3_2 13 156 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 156 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 185
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 156 185 (accept_3_2 10 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  156 185 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 156 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 156 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 185 (accept_3_2 7 156 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 156 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 156 185 (accept_3_2 4 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  156 185 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 156 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 156 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 156 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 185 (accept_3_2 1 156 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 156 185)))))))))))))))))))))))))))))) (allB_succ' 31 155 185 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 155 185 5 6 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 155 185 (Polychromatic418967fa.accept_20_9_15_5_1_4670 29 155 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 185 (accept_3_2 28 155 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 155 185 (Polychromatic418967fa.accept_17_10_2_15_1_3179 27 155 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 155 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 155 185 5 5 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 155 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 155 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 155 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 185 (accept_3_2 22 155 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 185 (Polychromatic418967fa.accept_9_3_2_5_1_234
  21 155 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 155 185 5 4 31 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 155 185
  (accept_3_2 19 155 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 155 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 155 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 155 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 185 (accept_3_2 16 155 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 155 185 5 3 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 155 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 155 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 185 (accept_3_2 13 155 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 155 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 155 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 155 185 5 2 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 155 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 155 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 155 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 185 (accept_3_2 7 155 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  155 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 155 185 5 1 31 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 155 185 (accept_3_2 4
  155 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 185
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 155 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 155 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 155 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 185 (accept_3_2 1 155 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 155 185))))))))))))))))))))))))))))))) (allB_succ' 32 154 185 (Eq.refl Bool.true) (allA_of_3_0
  32 154 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 153 185 (Eq.refl Bool.true) (allA_succ_of_accept 32
  153 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 153 185 (accept_3_2 31 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 153 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 153 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 185 (Polychromatic418967fa.accept_19_10_1_14_1_9224 29 153
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 185 (accept_3_2 28 153
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 185
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 153 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 185 (accept_3_2 25 153 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 185 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 153 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 185
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 185 (accept_3_2 22 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 185 (Polychromatic418967fa.accept_15_6_3_5_1_607 21 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 185 (accept_3_2 19 153 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 153 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 185
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 185 (accept_3_2 16 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 153 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 185 (accept_3_2 13 153 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 185 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 153 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 185
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 185 (accept_3_2 10 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 185 (accept_3_2 7 153 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 185 (Polychromatic418967fa.accept_13_6_10_3_1_897 6 153 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 185
  (Polychromatic418967fa.accept_24_5_9_17_1_8872 5 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 185 (accept_3_2 4 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 153 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 153 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 185 (accept_3_2 1 153 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 185))))))))))))))))))))))))))))))))) (allB_succ' 34 152 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 152 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 185 (Polychromatic418967fa.accept_13_6_9_3_1_915 32 152
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 152 185 (accept_3_2 31 152
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 152 185
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 152 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 152 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 185 (accept_3_2 28 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 152 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 185 (Polychromatic418967fa.accept_12_2_8_5_1_408
  26 152 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 152 185 (accept_3_2 25
  152 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 152 185
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 152 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 152 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 185 (accept_3_2 22 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 152 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 185 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 152 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 185 (accept_3_2 19
  152 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 152 185
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 152 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 152 185 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 185 (accept_3_2 16 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 152 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 185 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 152 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 185 (accept_3_2 13
  152 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 152 185
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 152 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 152 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 185 (accept_3_2 10 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 152 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 185 (Polychromatic418967fa.accept_7_1_5_3_1_268 8
  152 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 185 (accept_3_2 7 152
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 152 185
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 152 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 152 185 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 185 (accept_3_2 4 152 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 152 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 185 (Polychromatic418967fa.accept_7_2_5_3_1_98 2
  152 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 185 (accept_3_2 1 152
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 185)))))))))))))))))))))))))))))))))) (allB_succ' 35 151
  185 (Eq.refl Bool.true) (allA_of_3_0 35 151 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 150 185
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 150 185 5 7 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 150 185 (accept_3_2 34 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 150 185 (Polychromatic418967fa.accept_17_16_14_15_1_1250 33 150 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 185
  (Polychromatic418967fa.accept_20_12_10_5_1_4661 32 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 150 185 (accept_3_2 31 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 185 5 6 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 150 185 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 150 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 185 (accept_3_2 28 150 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 185 (Polychromatic418967fa.accept_9_8_6_5_1_513
  26 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 150 185 5 5 30 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 150 185
  (Polychromatic418967fa.accept_11_2_7_9_1_890 24 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 150 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 150 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 185 (accept_3_2 22 150 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 150 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 150 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 185 5 4 30 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 185 (accept_3_2 19 150 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 185 (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 150
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 150 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 150 185 (accept_3_2 16 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  150 185 5 3 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 150 185 (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 150 185 (accept_3_2 13 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 150 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 150 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 150 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 150 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 185 5 2 30 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 185
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 150 185 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 150 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 185 (accept_3_2 7 150 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 150 185 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 150 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 150 185 5 1 30 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 150 185 (accept_3_2 4 150 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 150 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 150 185 (accept_3_2 1 150 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  185)))))))))))))))))))))))))))))))))))) (allB_succ' 37 149 185 (Eq.refl Bool.true) (allA_succ_of_accept 36 149 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 149 185 (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 149 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 185 (accept_3_2 34 149 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 149 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 149 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 185
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 185 (accept_3_2 31 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 185 (Polychromatic418967fa.accept_16_14_5_9_1_5901 30 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 149 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 185 (accept_3_2 28 149 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 149 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 185
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 185 (accept_3_2 25 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 185 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 185 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 149 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 185 (accept_3_2 22 149 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 185 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 149 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 185
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 185 (accept_3_2 19 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 185 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 185 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 149 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 185 (accept_3_2 16 149 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 185 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 149 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 185
  (Polychromatic418967fa.accept_10_4_9_5_1_84 14 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 185 (accept_3_2 13 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 185 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 149 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 185 (accept_3_2 10 149 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 185 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 149 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 185
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 185 (accept_3_2 7 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 185 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 185 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 149 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 185 (accept_3_2 4 149 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 185 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 149 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 185
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 185 (accept_3_2 1 149 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  185))))))))))))))))))))))))))))))))))))) (allB_succ' 38 148 185 (Eq.refl Bool.true) (allA_of_3_0 38 148 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 147 185 (Eq.refl Bool.true) (allA_succ_of_accept 38 147 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 185 (accept_3_2 37 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 147 185 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 147 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 147 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 185 (accept_3_2 34 147 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 147 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 185 (accept_3_2 31 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 147 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 147 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 147 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 185 (accept_3_2 28 147 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 185 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 147 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 185 (accept_3_2 25 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 147 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 147 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 147 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 185 (accept_3_2 22 147 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 147
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 185 (accept_3_2 19 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 147 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 147 185 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 147 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 185 (accept_3_2 16 147 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 185 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 147 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 185 (accept_3_2 13 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 147 185 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 185 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 147 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 185 (accept_3_2 10 147 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 185 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 147 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 185
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 185 (accept_3_2 7 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  147 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 147 185 (Polychromatic418967fa.accept_17_5_11_15_1_5445 5 147 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 185 (accept_3_2 4 147 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 185 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 147 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 185
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 185 (accept_3_2 1 147 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  185))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 146 185 (Eq.refl Bool.true) (allA_succ_of_accept 39 146 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 146 185 (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 146 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 146 185 (accept_3_2 37 146 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 146 185 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 146 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 146 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 146 185 (accept_3_2 34 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 146 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 146 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 146 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 146 185 (accept_3_2 31 146 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 146 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 146 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 146 185
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 146 185 (accept_3_2 28 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 146 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 146 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 146 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 146 185 (accept_3_2 25 146 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 146 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 146 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 146 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 146 185 (accept_3_2 22 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 146 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 146 185 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 146 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 146 185 (accept_3_2 19 146 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 146 185 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 146 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 185
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 146 185 (accept_3_2 16 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 146 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 146 185 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 146 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 185 (accept_3_2 13 146 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 185 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 146 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 185
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 146 185 (accept_3_2 10 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  146 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 146 185 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 146 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 185 (accept_3_2 7 146 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 185 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 146 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 185
  (Polychromatic418967fa.accept_17_5_10_15_1_5574 5 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 146 185 (accept_3_2 4 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  146 185 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 146 185 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 146 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 185 (accept_3_2 1 146 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 146 185)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 145 185 (Eq.refl
  Bool.true) (allA_of_3_0 41 145 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 144 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 144 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 144 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 185 (accept_3_2 40 144 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 144 185 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 144 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 185
  (Polychromatic418967fa.accept_23_15_6_1_1_10656 38 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 144 185 (accept_3_2 37 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 144 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 144 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 144 185 (Polychromatic418967fa.accept_14_7_4_3_1_488 35 144
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 185 (accept_3_2 34 144
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 185
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 144 185 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 144 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 185 (accept_3_2 31 144 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 144 185 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 144 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 185
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 144 185 (accept_3_2 28 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 144 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 144 185 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 144 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 185 (accept_3_2 25 144 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 185 (Polychromatic418967fa.accept_13_11_1_3_1_910 24 144
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 185
  (Polychromatic418967fa.accept_17_6_8_15_1_10655 23 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 144 185 (accept_3_2 22 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 144 185 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 144 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 144 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 185 (accept_3_2 19 144 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 185 (Polychromatic418967fa.accept_13_5_1_3_1_878
  18 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 185
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 144 185 (accept_3_2 16 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 144 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 144 185 (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 144 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 185 (accept_3_2 13 144 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 185 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 144
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 185
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 185 (accept_3_2 10 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  144 185 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 144 185 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 144 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 185 (accept_3_2 7 144 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 185 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 144 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 185
  (Polychromatic418967fa.accept_13_5_1_3_1_878 5 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 185 (accept_3_2 4 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  144 185 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 144 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 144 185 (Polychromatic418967fa.accept_13_2_1_3_1_419 2 144 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 185 (accept_3_2 1 144 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 144 185)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 143 185 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 143 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 185
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 185 (accept_3_2 40 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 185 (accept_3_2 37 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 185 (Polychromatic418967fa.accept_17_2_7_15_1_5525 36 143 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 185
  (Polychromatic418967fa.accept_20_15_3_5_1_10654 35 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 143 185 (accept_3_2 34 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 143 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 143 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 185 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 143
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 185 (accept_3_2 31 143
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 185 (Polychromatic418967fa.accept_4_2_3_1_1_2
  30 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 185 (accept_3_2 28 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 185 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 185 (accept_3_2 25 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 143 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 185
  (Polychromatic418967fa.accept_19_4_10_14_1_7833 23 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 143 185 (accept_3_2 22 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 143 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 143 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 185 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 143 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 185 (accept_3_2 19 143 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 185
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 185 (accept_3_2 16 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 185 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 185 (accept_3_2 13 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 143 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 185
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 185 (accept_3_2 10 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 185 (Polychromatic418967fa.accept_17_9_7_15_1_4346 9 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 185 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 185 (accept_3_2 7 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 143 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 185
  (Polychromatic418967fa.accept_17_5_7_15_1_1230 5 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 185 (accept_3_2 4 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 185 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 143 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 185 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 185 (accept_3_2 1 143 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 185))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 142 185 (Eq.refl
  Bool.true) (allA_of_3_0 44 142 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 141 185 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 141 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 141 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 185 (accept_3_2 43 141 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 185 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 141 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 185
  (Polychromatic418967fa.accept_13_2_11_3_1_873 41 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 185 (accept_3_2 40 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 185 (accept_3_2 37 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 185 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 141 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 185 (accept_3_2 34 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 185 (accept_3_2 31 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 141 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 185
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 185 (accept_3_2 28 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 185 (accept_3_2 25 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 185 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 141 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 185
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 185 (accept_3_2 22 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 185 (accept_3_2 19 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 185 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 141 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 185
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 185 (accept_3_2 16 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 185 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 185 (accept_3_2 13 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 185 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 141 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 185
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 185 (accept_3_2 10 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 185 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 185 (accept_3_2 7 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 185 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 141 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 185
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 185 (accept_3_2 4 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 185 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 141 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 185 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 185 (accept_3_2 1 141 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 185))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 140 185 (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 140 185 5 9 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 140 185 (Polychromatic418967fa.accept_17_10_4_15_1_2165 44 140 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 140 185 (accept_3_2 43 140 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 140 185 (Polychromatic418967fa.accept_19_4_7_14_1_3537 42 140
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 140 185
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 140 185 5 8 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 140 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 140 185 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 140
  185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 185 (accept_3_2 37 140
  185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 140 185
  (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 140 185 5 7 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 140 185 (accept_3_2 34 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 140 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 140 185 (Polychromatic418967fa.accept_11_10_8_9_1_492 32 140 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 140 185 (accept_3_2 31 140 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 185 5 6 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 185 (Polychromatic418967fa.accept_8_5_4_1_1_111 29
  140 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 185 (accept_3_2 28
  140 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 185
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 140 185 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 140 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 140 185 5 5 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 140 185
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 185 (Polychromatic418967fa.accept_19_4_7_14_1_3537 23 140 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 185 (accept_3_2 22 140 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 140 185 5 4 28 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 185 (accept_3_2 19
  140 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 185
  (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 140 185 (Polychromatic418967fa.accept_22_17_8_9_1_10653 17 140 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 185 (accept_3_2 16 140 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 140 185 5 3 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 140 185 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 140 185
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 140 185 (accept_3_2 13 140 185
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 185
  (Polychromatic418967fa.accept_19_12_7_14_1_10637 12 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 185 (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 140 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 185 5 2 28 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 185
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 140 185 (Polychromatic418967fa.accept_16_8_12_9_1_2569 8 140 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 185 (accept_3_2 7 140 185 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 140 185 (Polychromatic418967fa.accept_13_6_10_3_1_897 6 140 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 140 185 5 1 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 140 185 (accept_3_2 4 140 185 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 185 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 185 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 185
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 185 (accept_3_2 1 140 185 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  185))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_185_segment_000)))))))))))))))))))))))))))))))))))))))))))))


