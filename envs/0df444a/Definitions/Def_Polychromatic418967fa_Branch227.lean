-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch227
-- name    : Polychromatic418967fa_Branch227
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:26:02.854356+00:00
-- url     : https://prove2.me/theorems/581cf6a8-451e-4bb0-9e7c-a372c6f1cee5
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch227_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_227 : allB 227 227 :=
  allB_succ' 2 226 227 (Eq.refl Bool.true) (allA_of_3_0 2 226 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  225 227 (Eq.refl Bool.true) (allA_succ_of_accept 2 225 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 225 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 227 (accept_3_2 1 225 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 227))) (allB_succ' 4 224 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 224 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 224 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 227 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 224 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 224 227 (accept_3_2 1 224 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224 227)))) (allB_succ' 5 223 227 (Eq.refl Bool.true) (allA_of_3_0
  5 223 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 222 227 (Eq.refl Bool.true) (allA_succ_of_accept 5
  222 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 222 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 222 227 (accept_3_2 4 222 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 222 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 222 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 222 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 227 (accept_3_2 1 222 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222 227)))))) (allB_succ' 7 221 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 221 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 221 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 227 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 221
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 227 (accept_3_2 4 221 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  221 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 221 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 227 (accept_3_2 1 221 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221 227)))))))
  (allB_succ' 8 220 227 (Eq.refl Bool.true) (allA_of_3_0 8 220 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 219 227 (Eq.refl Bool.true) (allA_succ_of_accept 8 219 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 219 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 227 (accept_3_2 7 219 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  219 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 219 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 227 (accept_3_2 4 219 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 227 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 219 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 219 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 227 (accept_3_2 1 219 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 219 227))))))))) (allB_succ' 10 218 227 (Eq.refl Bool.true) (allA_succ_of_accept 9 218
  227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 218 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 218 227 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 218 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 218 227 (accept_3_2 7 218 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 218 227 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 218 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 218 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  218 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 218 227 (accept_3_2 4 218
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 218 227 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 218 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 218 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 218 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 218 227 (accept_3_2 1 218 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  227)))))))))) (allB_succ' 11 217 227 (Eq.refl Bool.true) (allA_of_3_0 11 217 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 216 227 (Eq.refl Bool.true) (allA_succ_of_accept 11 216 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 216 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 216 227 (accept_3_2 10 216 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  216 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 216 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 216 227 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 216 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 227 (accept_3_2 7 216 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 216 227 (Polychromatic418967fa.accept_19_6_7_18_1_120 6 216 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 227
  (Polychromatic418967fa.accept_16_5_8_3_1_4240 5 216 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 216 227 (accept_3_2 4 216 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  216 227 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 216 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 216 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 216 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 227 (accept_3_2 1 216 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 216 227)))))))))))) (allB_succ' 13 215 227 (Eq.refl Bool.true) (allA_succ_of_accept 12
  215 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 215 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 215 227 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 215 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 227 (accept_3_2 10 215 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 215 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 215 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 227
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 215 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 215 227 (accept_3_2 7 215 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  215 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 215 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 215 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 215 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 227 (accept_3_2 4 215 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 215 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 215 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 227 (accept_3_2 1 215 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  227))))))))))))) (allB_succ' 14 214 227 (Eq.refl Bool.true) (allA_of_3_0 14 214 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 213 227 (Eq.refl Bool.true) (allA_succ_of_accept 14 213 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 213 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 227 (accept_3_2 13 213 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 213 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 213 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 213 227 (Polychromatic418967fa.accept_13_11_5_6_1_519 11 213 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 227 (accept_3_2 10 213 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 227 (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 213
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 227 (accept_3_2 7 213 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  213 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 213 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 213 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 213 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 227 (accept_3_2 4 213 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 213 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 213 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 227 (accept_3_2 1 213 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  227))))))))))))))) (allB_succ' 16 212 227 (Eq.refl Bool.true) (allA_succ_of_accept 15 212 227
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 212 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 212 227 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 212 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 212 227 (accept_3_2 13 212 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 212 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 212 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 212 227
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 212 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 212 227 (accept_3_2 10 212 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  212 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 212 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 212 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 227 (accept_3_2 7 212 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 212 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 212 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 212 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 212 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 212 227 (accept_3_2 4 212 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  212 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 212 227 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 212 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 227 (accept_3_2 1 212 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 227)))))))))))))))) (allB_succ' 17 211 227 (Eq.refl Bool.true) (allA_of_3_0 17 211
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 210 227 (Eq.refl Bool.true) (allA_succ_of_accept 17 210
  227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 210 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 210 227 (accept_3_2 16 210 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 210 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 210 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 210 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 210 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 210 227 (accept_3_2 13 210 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 210 227 (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 210 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 210 227
  (Polychromatic418967fa.accept_19_11_1_18_1_5276 11 210 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 210 227 (accept_3_2 10 210 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 210 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 210 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 210 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 227 (accept_3_2 7 210 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 210 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 6
  210 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 210 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 210 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 210 227 (accept_3_2 4 210 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  210 227 (Polychromatic418967fa.accept_20_3_10_7_1_7839 3 210 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 210 227 (Polychromatic418967fa.accept_19_2_1_18_1_2660 2 210 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 227 (accept_3_2 1 210 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 210 227)))))))))))))))))) (allB_succ' 19 209 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 209 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 209 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 227 (Polychromatic418967fa.accept_20_17_9_7_1_13576 17 209
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 227 (accept_3_2 16 209
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 227
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 209 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 209 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 209 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 227 (accept_3_2 13 209 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 209 227 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 209 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 209 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 227 (accept_3_2 10 209 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 209 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 227 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 209 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 227 (accept_3_2 7 209 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 209 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 227
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 209 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 227 (accept_3_2 4 209 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 227 (Polychromatic418967fa.accept_13_3_1_6_1_509 3 209 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 209 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 227 (accept_3_2 1 209 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 227))))))))))))))))))) (allB_succ' 20 208 227 (Eq.refl Bool.true) (allA_of_3_0 20
  208 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 207 227 (Eq.refl Bool.true) (allA_succ_of_accept 20
  207 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 207 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 207 227 (accept_3_2 19 207 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 207 227 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 207 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 227 (Polychromatic418967fa.accept_31_17_21_10_1_13585 17
  207 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 227 (accept_3_2 16
  207 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 227
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 207 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 207 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 207 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 227 (accept_3_2 13 207 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 207 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 207 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 227
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 207 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 207 227 (accept_3_2 10 207 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 207 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 207 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 227 (accept_3_2 7 207 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  207 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 227
  (Polychromatic418967fa.accept_11_5_9_7_1_411 5 207 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 227 (accept_3_2 4 207 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 227 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 207 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 207 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 227 (accept_3_2 1 207 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 207 227))))))))))))))))))))) (allB_succ' 22 206 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 206 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 206 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 206 227 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 206
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 206 227 (accept_3_2 19 206
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 206 227
  (Polychromatic418967fa.accept_13_5_11_6_1_505 18 206 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 206 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 206 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 206 227 (accept_3_2 16 206 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 206 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 206 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 206 227 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 206 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 206 227 (accept_3_2 13
  206 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 206 227
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 206 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 206 227 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 206 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 227 (accept_3_2 10 206 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 206 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 206 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 206 227 (Polychromatic418967fa.accept_12_8_2_11_1_246
  8 206 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 206 227 (accept_3_2 7
  206 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 206 227
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 206 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 206 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 206 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 227 (accept_3_2 4 206 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 206 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 206 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 227
  (Polychromatic418967fa.accept_19_2_16_18_1_10922 2 206 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 206 227 (accept_3_2 1 206 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  206 227)))))))))))))))))))))) (allB_succ' 23 205 227 (Eq.refl Bool.true) (allA_of_3_0 23 205 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 24 204 227 (Eq.refl Bool.true) (allA_succ_of_accept 23 204 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 204 227 (accept_3_2 22 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 204 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 204 227 (Polychromatic418967fa.accept_13_7_9_6_1_148 20 204 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 227 (accept_3_2 19 204 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 204 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 204 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 204 227 (accept_3_2 16 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 204 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 204 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 204 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 227 (accept_3_2 13 204 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 204 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 204 227
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 204 227 (accept_3_2 10 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  204 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 204 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 204 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 227 (accept_3_2 7 204 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 227 (Polychromatic418967fa.accept_21_6_15_17_1_7388 6 204 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 204 227
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 204 227 (accept_3_2 4 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  204 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 204 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 204 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 204 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 227 (accept_3_2 1 204 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 204 227)))))))))))))))))))))))) (allB_succ' 25 203 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 24 203 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 203 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 227 (Polychromatic418967fa.accept_16_7_11_3_1_1330 23 203
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 227 (accept_3_2 22 203
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 227
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 203 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 203 227 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 203 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 227 (accept_3_2 19 203 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 203 227 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 203 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 203 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 227 (accept_3_2 16 203 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 203 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 227 (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 203 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 227 (accept_3_2 13 203 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 203 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 227
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 203 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 203 227 (accept_3_2 10 203 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  203 227 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 203 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 203 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 203 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 227 (accept_3_2 7 203 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 203 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 227
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 203 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 227 (accept_3_2 4 203 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 203 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 227 (Polychromatic418967fa.accept_13_2_8_6_1_2390 2 203 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 227 (accept_3_2 1 203 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 227))))))))))))))))))))))))) (allB_succ' 26 202 227 (Eq.refl Bool.true)
  (allA_of_3_0 26 202 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 201 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 201 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 201 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 227 (accept_3_2 25 201 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 201 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 201 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  201 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 227 (accept_3_2 22
  201 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 227
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 201 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 201 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 201 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 227 (accept_3_2 19 201 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 201 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 201 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 227 (Polychromatic418967fa.accept_9_8_3_2_1_417
  17 201 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 227 (accept_3_2 16
  201 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 227
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 201 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 201 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 201 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 227 (accept_3_2 13 201 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 201 227 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 201 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 227
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 11 201 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 227 (accept_3_2 10 201 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  201 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 201 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 201 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 227 (accept_3_2 7 201 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 201 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 201 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 227 (accept_3_2 4 201 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 201 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 201 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 227 (accept_3_2 1 201 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 227))))))))))))))))))))))))))) (allB_succ' 28 200 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 200 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 200 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 227 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 200
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 200 227 (accept_3_2 25 200
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 200 227
  (Polychromatic418967fa.accept_13_11_5_6_1_519 24 200 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 200 227 (Polychromatic418967fa.accept_13_10_5_6_1_1671 23 200 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 227 (accept_3_2 22 200 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 200 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 200 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 200 227 (Polychromatic418967fa.accept_7_6_4_3_1_266
  20 200 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 200 227 (accept_3_2 19
  200 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 200 227
  (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 200 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 200 227 (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 200 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 200 227 (accept_3_2 16 200 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 200 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 200 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 200 227 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 200 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 200 227 (accept_3_2 13
  200 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 200 227
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 12 200 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 200 227 (Polychromatic418967fa.accept_13_11_5_6_1_519 11 200 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 200 227 (accept_3_2 10 200 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 200 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 8
  200 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 200 227 (accept_3_2 7 200
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 200 227
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 200 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 200 227 (Polychromatic418967fa.accept_16_5_8_3_1_4240 5 200 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 227 (accept_3_2 4 200 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 200 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 227 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  200 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 200 227 (accept_3_2 1 200
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200 227)))))))))))))))))))))))))))) (allB_succ' 29 199 227
  (Eq.refl Bool.true) (allA_of_3_0 29 199 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 198 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 198 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 198 227 (accept_3_2 28 198 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 198 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 198 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 198 227 (accept_3_2 25 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 198 227 (Polychromatic418967fa.accept_21_3_9_17_1_2983 24 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 198 227 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 198 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 198 227 (accept_3_2 22 198 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 198 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 198 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 227
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 198 227 (accept_3_2 19 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 198 227 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 198 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 198 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 198 227 (accept_3_2 16 198 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 198 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 198 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 227
  (Polychromatic418967fa.accept_13_1_3_6_1_158 14 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 198 227 (accept_3_2 13 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 198 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 198 227 (Polychromatic418967fa.accept_16_11_6_3_1_6564 11 198 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 198 227 (accept_3_2 10 198 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 198 227 (accept_3_2 7 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  198 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 198 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 198 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 198 227 (accept_3_2 4 198 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 198 227 (Polychromatic418967fa.accept_21_3_9_17_1_2983 3 198 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 227
  (Polychromatic418967fa.accept_16_2_6_3_1_5396 2 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 198 227 (accept_3_2 1 198 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  227)))))))))))))))))))))))))))))) (allB_succ' 31 197 227 (Eq.refl Bool.true) (allA_succ_of_accept 30 197 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 197 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 197 227 (Polychromatic418967fa.accept_17_12_10_6_1_3691 29 197 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 227 (accept_3_2 28 197 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 227 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 197 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 197 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 227 (accept_3_2 25 197 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 197 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 197 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 227 (accept_3_2 22 197 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 197 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 227
  (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 197 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 197 227 (accept_3_2 19 197 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 197 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 197 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 227 (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 197
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 227 (accept_3_2 16 197
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 227
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 197 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 197 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 197 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 227 (accept_3_2 13 197 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 197 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 197 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 227 (Polychromatic418967fa.accept_7_4_1_3_1_277
  11 197 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 227 (accept_3_2 10
  197 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 197 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 197 227 (Polychromatic418967fa.accept_13_8_2_6_1_2385 8 197 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 227 (accept_3_2 7 197 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 197 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 197 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  197 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 227 (accept_3_2 4 197
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 227
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 197 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 197 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 197 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 227 (accept_3_2 1 197 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 197 227))))))))))))))))))))))))))))))) (allB_succ' 32 196 227 (Eq.refl Bool.true) (allA_of_3_0
  32 196 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 195 227 (Eq.refl Bool.true) (allA_succ_of_accept 32
  195 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 195 227 (accept_3_2 31 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 195 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 195 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 227 (Polychromatic418967fa.accept_19_10_5_18_1_10817 29
  195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 227 (accept_3_2 28
  195 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 227
  (Polychromatic418967fa.accept_18_9_15_11_1_5693 27 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 195 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 195 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 227 (accept_3_2 25 195 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 227 (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 195 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 227 (accept_3_2 22 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 195 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 195 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 195 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 227 (accept_3_2 19 195 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 195 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 227 (accept_3_2 16 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 195 227 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 195 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 227 (accept_3_2 13 195 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 195 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 227 (accept_3_2 10 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 227 (accept_3_2 7 195 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 227 (Polychromatic418967fa.accept_18_6_15_11_1_3141 6 195 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 227 (accept_3_2 4 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 195 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 195 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 227 (accept_3_2 1 195 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 195 227))))))))))))))))))))))))))))))))) (allB_succ' 34 194 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 194 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 194 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 194 227 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 194
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 194 227 (accept_3_2 31 194
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 194 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 194 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 194 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 227 (accept_3_2 28 194 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 194 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 194 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 194 227 (Polychromatic418967fa.accept_9_8_5_2_1_422
  26 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 194 227 (accept_3_2 25
  194 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 194 227
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 194 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 194 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 194 227 (accept_3_2 22 194 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 194 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 194 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 194 227 (Polychromatic418967fa.accept_12_8_2_11_1_246
  20 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 194 227 (accept_3_2 19
  194 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 194 227
  (Polychromatic418967fa.accept_13_5_12_6_1_508 18 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 194 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 194 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 194 227 (accept_3_2 16 194 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 194 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 194 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 194 227
  (Polychromatic418967fa.accept_17_14_7_6_1_11222 14 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 194 227 (accept_3_2 13 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 194 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 194 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 194 227 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 194
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 227 (accept_3_2 10 194
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 227 (Polychromatic418967fa.accept_4_1_2_3_1_9
  9 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 227
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 227 (accept_3_2 7 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 194 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 227 (accept_3_2 4 194 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 194 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 227 (accept_3_2 1 194 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  227)))))))))))))))))))))))))))))))))) (allB_succ' 35 193 227 (Eq.refl Bool.true) (allA_of_3_0 35 193 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 192 227 (Eq.refl Bool.true) (allA_succ_of_accept 35 192 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 192 227 (accept_3_2 34 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 192 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 192 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 192 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 192 227 (accept_3_2 31 192 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 192 227 (Polychromatic418967fa.accept_13_4_10_6_1_989 30 192 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 192 227
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 192 227 (accept_3_2 28 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 192 227 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 192 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 192 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 227 (accept_3_2 25 192 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 192 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 192 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 192 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 192 227 (accept_3_2 22 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 192 227 (Polychromatic418967fa.accept_14_7_10_3_1_1034 21 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 192 227 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 192 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 192 227 (accept_3_2 19 192 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 192 227 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 192
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 192 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 192 227 (accept_3_2 16 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 192 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 192 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 192 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 227 (accept_3_2 13 192 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 227 (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 192 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 227
  (Polychromatic418967fa.accept_17_11_5_6_1_4928 11 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 192 227 (accept_3_2 10 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  192 227 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 192 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 192 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 227 (accept_3_2 7 192 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 192 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 192 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 192 227 (accept_3_2 4 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  192 227 (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 192 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 192 227 (Polychromatic418967fa.accept_13_2_10_6_1_1676 2 192 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 227 (accept_3_2 1 192 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192 227)))))))))))))))))))))))))))))))))))) (allB_succ' 37 191 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 36 191 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 191 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 227
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 227 (accept_3_2 34 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 227 (Polychromatic418967fa.accept_19_13_1_18_1_5279 32 191 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 227 (accept_3_2 31 191 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 227 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 191
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 227 (accept_3_2 28 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 191 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 227 (accept_3_2 25 191 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 227 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 191 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 227
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 227 (accept_3_2 22 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 227 (Polychromatic418967fa.accept_15_6_11_2_1_2801 21 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 191 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 227 (accept_3_2 19 191 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 227 (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 191 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 227
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 227 (accept_3_2 16 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 227 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 191 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 227 (accept_3_2 13 191 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 191 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 227
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 191 227 (accept_3_2 10 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 191 227 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 191 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 191 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 227 (accept_3_2 7 191 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 227 (accept_3_2 4 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 227 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 191 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 227 (Polychromatic418967fa.accept_13_2_9_6_1_501 2 191 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 227 (accept_3_2 1 191 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 227))))))))))))))))))))))))))))))))))))) (allB_succ' 38 190 227 (Eq.refl Bool.true)
  (allA_of_3_0 38 190 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 189 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 189 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 189 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 227 (accept_3_2 37 189 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 189 227 (Polychromatic418967fa.accept_20_16_9_7_1_3402 36 189 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 227
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 35 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 189 227 (accept_3_2 34 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 189 227 (Polychromatic418967fa.accept_16_1_13_3_1_2168 33 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 227 (accept_3_2 31 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 189 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 227
  (Polychromatic418967fa.accept_17_12_2_6_1_2630 29 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 227 (accept_3_2 28 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 189 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 227 (accept_3_2 25 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 227 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 189 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 227
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 227 (accept_3_2 22 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 189 227 (Polychromatic418967fa.accept_17_4_2_6_1_2629 21 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 189 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 227 (accept_3_2 19 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 189 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 227
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 17 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 227 (accept_3_2 16 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 227 (accept_3_2 13 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 227 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 189 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 227
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 227 (accept_3_2 10 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 227 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 227 (accept_3_2 7 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 189 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 227
  (Polychromatic418967fa.accept_20_5_9_7_1_10766 5 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 227 (accept_3_2 4 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 189 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 227 (accept_3_2 1 189 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 189 227))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 188 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 188 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 188 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 188 227 (Polychromatic418967fa.accept_12_2_8_11_1_31
  38 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 188 227 (accept_3_2 37
  188 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 188 227
  (Polychromatic418967fa.accept_15_6_8_2_1_104 36 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 188 227 (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 188 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 188 227 (accept_3_2 34 188 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 188 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 188 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 188 227 (Polychromatic418967fa.accept_7_4_6_3_1_271
  32 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 188 227 (accept_3_2 31
  188 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 188 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 188 227 (Polychromatic418967fa.accept_10_9_8_7_1_714 29 188 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 188 227 (accept_3_2 28 188 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 188 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 188 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 188 227 (Polychromatic418967fa.accept_12_2_8_11_1_31
  26 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 188 227 (accept_3_2 25
  188 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 188 227
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 188 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 188 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 188 227 (accept_3_2 22 188 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 188 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 188 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 188 227
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 20 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 188 227 (accept_3_2 19 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 188 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 188 227 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 188 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 188 227 (accept_3_2 16 188 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 188 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 188 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 188 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 188 227 (accept_3_2 13 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 188 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 188 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 188 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 188 227 (accept_3_2 10 188 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 188 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 188 227
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 8 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 188 227 (accept_3_2 7 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  188 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 188 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 188 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 188 227 (accept_3_2 4 188 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 188 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 188 227 (accept_3_2 1 188 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  227)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 187 227 (Eq.refl Bool.true) (allA_of_3_0 41 187 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 186 227 (Eq.refl Bool.true) (allA_succ_of_accept 41 186 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 186 227 (accept_3_2 40 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 186 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 186 227 (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 186 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 186 227 (accept_3_2 37 186 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 186 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 186 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 186 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 186 227 (accept_3_2 34 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 186 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 186 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 186 227 (accept_3_2 31 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 186 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 186 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 186 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 186 227 (accept_3_2 28 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 186 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 186 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 186 227 (accept_3_2 25 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 186 227 (Polychromatic418967fa.accept_13_11_4_6_1_1006 24 186 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 186 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 186 227 (accept_3_2 22 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 186 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 186 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 227 (accept_3_2 19 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 227 (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 186 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 186 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 186 227 (accept_3_2 16 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 186 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 186 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 227 (accept_3_2 13 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 186 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 186 227
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 186 227 (accept_3_2 10 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  186 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 186 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 227 (accept_3_2 7 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 186 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 186 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 186 227 (accept_3_2 4 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  186 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 186 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 186 227 (Polychromatic418967fa.accept_13_2_4_6_1_2356 2 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 227 (accept_3_2 1 186 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 186 227)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 185 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 185 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 185 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 227 (Polychromatic418967fa.accept_15_11_5_2_1_520
  41 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 227 (accept_3_2 40
  185 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 185 227
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 185 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 185 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 227 (accept_3_2 37 185 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 185 227 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 185 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 185 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 185 227 (accept_3_2 34 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 185 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 185 227 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 185 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 185 227 (accept_3_2 31 185 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 185 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 185 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 185 227
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 185 227 (accept_3_2 28 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 185 227 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 185 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 185 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 185 227 (accept_3_2 25 185 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 185 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 185 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 185 227
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 185 227 (accept_3_2 22 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 185 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 185 227 (Polychromatic418967fa.accept_19_1_14_18_1_3919 20 185 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 227 (accept_3_2 19 185 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 185 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 185 227 (accept_3_2 16 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 185 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 185 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 185 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 227 (accept_3_2 13 185 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 185 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 227
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 185 227 (accept_3_2 10 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  185 227 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 185 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 185 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 227 (accept_3_2 7 185 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 185 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 227
  (Polychromatic418967fa.accept_11_5_9_7_1_411 5 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 185 227 (accept_3_2 4 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  185 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 185 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 185 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 185 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 227 (accept_3_2 1 185 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 185 227))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 184 227 (Eq.refl
  Bool.true) (allA_of_3_0 44 184 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 183 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 183 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 227 (accept_3_2 43 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 183 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 183 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 227 (Polychromatic418967fa.accept_9_5_3_2_1_171
  41 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 227 (accept_3_2 40
  183 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 227
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 183 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 227 (accept_3_2 37 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 183 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 183 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 227 (Polychromatic418967fa.accept_9_8_3_2_1_417
  35 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 227 (accept_3_2 34
  183 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 227
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 183 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 227 (accept_3_2 31 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 183 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 183 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 227 (Polychromatic418967fa.accept_13_3_1_6_1_509
  29 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 227 (accept_3_2 28
  183 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 227
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 183 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 227 (accept_3_2 25 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 183 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 183 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 227 (Polychromatic418967fa.accept_7_2_1_3_1_102
  23 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 227 (accept_3_2 22
  183 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 227
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 227 (accept_3_2 19 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 183 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 227 (Polychromatic418967fa.accept_9_8_3_2_1_417
  17 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 227 (accept_3_2 16
  183 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 227
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 183 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 227 (accept_3_2 13 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 183 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 183 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 227 (Polychromatic418967fa.accept_7_4_1_3_1_277
  11 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 227 (accept_3_2 10
  183 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 183 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 227 (accept_3_2 7 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 183 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 183 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 227 (accept_3_2 4 183
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 227
  (Polychromatic418967fa.accept_13_3_1_6_1_509 3 183 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 227 (accept_3_2 1 183 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183 227))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 182 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 182 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 182 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 182 227 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 182
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 182 227 (accept_3_2 43 182
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 182 227
  (Polychromatic418967fa.accept_19_4_11_18_1_3909 42 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 182 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 182 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 182 227 (accept_3_2 40 182 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 182 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 182 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 182 227
  (Polychromatic418967fa.accept_20_18_2_7_1_6285 38 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 182 227 (accept_3_2 37 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 182 227 (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 182 227 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 182 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 182 227 (accept_3_2 34 182 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 182 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 182 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 182 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 182 227 (accept_3_2 31 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 182 227 (Polychromatic418967fa.accept_21_9_14_17_1_12039 30 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 182 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 182 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 182 227 (accept_3_2 28 182 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 182 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 182 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 182 227
  (Polychromatic418967fa.accept_19_7_11_18_1_6680 26 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 182 227 (accept_3_2 25 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 182 227 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 182 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 182 227 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 182
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 227 (accept_3_2 22 182
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 182 227 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 182 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 182 227 (accept_3_2 19 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 182 227 (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 182 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 182 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 227 (accept_3_2 16 182 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 182 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 182 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 182 227
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 182 227 (accept_3_2 13 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 182 227 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 182 227 (Polychromatic418967fa.accept_16_11_6_3_1_6564 11 182 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 227 (accept_3_2 10 182 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 182 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 182 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 182 227 (accept_3_2 7 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  182 227 (Polychromatic418967fa.accept_19_6_11_18_1_12181 6 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 182 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 182 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 227 (accept_3_2 4 182 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 182 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 227
  (Polychromatic418967fa.accept_16_2_6_3_1_5396 2 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 182 227 (accept_3_2 1 182 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  227)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 181 227 (Eq.refl Bool.true) (allA_of_3_0 47 181 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 180 227 (Eq.refl Bool.true) (allA_succ_of_accept 47 180 227
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 180 227 (accept_3_2 46 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 180 227 (Polychromatic418967fa.accept_21_3_12_17_1_7471 45 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 180 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 180 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 180 227 (accept_3_2 43 180 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 180 227 (Polychromatic418967fa.accept_24_18_12_11_1_11858 42 180 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 180 227
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 180 227 (accept_3_2 40 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 180 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 180 227 (Polychromatic418967fa.accept_16_6_4_3_1_2189 38 180 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 180 227 (accept_3_2 37 180 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 180 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 180 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 180 227
  (Polychromatic418967fa.accept_19_16_9_18_1_8127 35 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 180 227 (accept_3_2 34 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 180 227 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 180 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 180 227 (Polychromatic418967fa.accept_19_13_9_18_1_10939 32
  180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 227 (accept_3_2 31
  180 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 180 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 180 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 180 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 227 (accept_3_2 28 180 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 180 227 (Polychromatic418967fa.accept_19_8_9_18_1_2704 27 180 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 180 227
  (Polychromatic418967fa.accept_21_5_12_17_1_10634 26 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 180 227 (accept_3_2 25 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 180 227 (Polychromatic418967fa.accept_16_8_4_3_1_3146 24 180 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 180 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 180 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 180 227 (accept_3_2 22 180 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 180 227
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 21 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 180 227 (Polychromatic418967fa.accept_24_20_12_11_1_8440 20 180 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 227 (accept_3_2 19 180 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 227 (Polychromatic418967fa.accept_13_5_11_6_1_505 18 180 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 180 227
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 17 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 180 227 (accept_3_2 16 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 180 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 180 227 (Polychromatic418967fa.accept_11_3_4_7_1_114 14 180 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 227 (accept_3_2 13 180 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 227 (Polychromatic418967fa.accept_16_12_4_3_1_4295 12 180
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 227
  (Polychromatic418967fa.accept_22_11_4_7_1_13584 11 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 180 227 (accept_3_2 10 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 180 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 180 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 180 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 227 (accept_3_2 7 180 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 227 (Polychromatic418967fa.accept_16_6_4_3_1_2189
  6 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 227
  (Polychromatic418967fa.accept_13_5_11_6_1_505 5 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 180 227 (accept_3_2 4 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  180 227 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 180 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 180 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 180 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 227 (accept_3_2 1 180 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 180 227)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 179 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 179 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 179 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 227
  (Polychromatic418967fa.accept_19_9_8_18_1_1571 47 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 179 227 (accept_3_2 46 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 179 227 (Polychromatic418967fa.accept_19_7_8_18_1_1576 45 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 179 227 (Polychromatic418967fa.accept_13_5_10_6_1_2361 44 179 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 227 (accept_3_2 43 179 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 179 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 179 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 227
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 179 227 (accept_3_2 40 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 179 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 179 227 (Polychromatic418967fa.accept_10_8_9_7_1_1118 38 179 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 227 (accept_3_2 37 179 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 179 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 227
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 179 227 (accept_3_2 34 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 179 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 179 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 179 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 227 (accept_3_2 31 179 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 179 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 227
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 179 227 (accept_3_2 28 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 179 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 179 227 (Polychromatic418967fa.accept_11_4_3_7_1_828 26 179 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 227 (accept_3_2 25 179 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 179 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 227 (accept_3_2 22 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 179 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 227 (accept_3_2 19 179 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 227 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 179 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 227
  (Polychromatic418967fa.accept_13_4_10_6_1_989 17 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 227 (accept_3_2 16 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 179 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 227 (accept_3_2 13 179 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 179 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 227
  (Polychromatic418967fa.accept_19_11_8_18_1_6631 11 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 179 227 (accept_3_2 10 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 179 227 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 179 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 179 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 227 (accept_3_2 7 179 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 227 (accept_3_2 4 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 179 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 227 (Polychromatic418967fa.accept_10_2_9_7_1_720 2 179 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 227 (accept_3_2 1 179 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 227))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 178 227
  (Eq.refl Bool.true) (allA_of_3_0 50 178 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 177 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 177 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 227 (accept_3_2 49 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 177 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 177 227 (accept_3_2 46 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 177 227 (Polychromatic418967fa.accept_16_13_1_3_1_2205 45 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 177 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 227 (accept_3_2 43 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 177 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 227
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 227 (accept_3_2 40 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 177 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 177 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 227 (accept_3_2 37 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 177 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 227 (accept_3_2 34 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 177 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 177 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 227 (accept_3_2 31 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 177 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 227 (accept_3_2 28 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 177 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 177 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 227 (accept_3_2 25 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 227 (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 177 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 227 (accept_3_2 22 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 177 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 177 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 227 (accept_3_2 19 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 177 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 227 (accept_3_2 16 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 177 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 227 (accept_3_2 13 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 177 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 227
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 227 (accept_3_2 10 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 227 (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 227 (accept_3_2 7 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 177 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 227 (accept_3_2 4 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 177 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 227 (accept_3_2 1 177 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177 227))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 176 227
  (Eq.refl Bool.true) (allA_succ_of_accept 51 176 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 176 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 176 227 (accept_3_2 49 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 176 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 176 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 176 227 (accept_3_2 46 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 176 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 176 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 176 227 (accept_3_2 43 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 176 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 176 227 (Polychromatic418967fa.accept_10_1_6_7_1_710 41 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 176 227 (accept_3_2 40 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 176 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 176 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 176 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 176 227 (accept_3_2 37 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 176 227 (Polychromatic418967fa.accept_15_6_11_2_1_2801 36 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 176 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 176 227 (accept_3_2 34 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 176 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 176 227
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 176 227 (accept_3_2 31 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 176 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 176 227 (Polychromatic418967fa.accept_19_10_5_18_1_10817 29 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 176 227 (accept_3_2 28 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 176 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 176 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 176 227
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 176 227 (accept_3_2 25 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 176 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 176 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 176 227 (accept_3_2 22 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 176 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 176 227
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 176 227 (accept_3_2 19 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 176 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 176 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 176 227 (accept_3_2 16 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 176 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 176 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 176 227 (accept_3_2 13 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 176 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 176 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 227 (accept_3_2 10 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 176 227 (accept_3_2 7 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  176 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 176 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 227 (accept_3_2 4 176 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 176 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 227 (accept_3_2 1 176 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  227)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 175 227 (Eq.refl Bool.true) (allA_of_3_0 53 175
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 174 227 (Eq.refl Bool.true) (allA_succ_of_accept 53 174
  227 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 174 227 (accept_3_2 52 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 174 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 174 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 174 227 (accept_3_2 49 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 174 227 (Polychromatic418967fa.accept_32_16_14_3_1_13583 48 174 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 174 227
  (Polychromatic418967fa.accept_19_9_3_18_1_5263 47 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 174 227 (accept_3_2 46 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 174 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 174 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 174 227 (accept_3_2 43 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 174 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 174 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 174 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 174 227 (accept_3_2 40 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 174 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 174 227 (Polychromatic418967fa.accept_11_5_9_7_1_411 38 174 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 227 (accept_3_2 37 174 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 174 227 (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 174
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 174 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 174 227 (accept_3_2 34 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 174 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 174 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 227 (accept_3_2 31 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 174 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 174 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 174 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 174 227 (accept_3_2 28 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 174 227 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 174 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 227 (accept_3_2 25 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 174 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 174 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 174 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 174 227 (accept_3_2 22 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 174 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 174 227 (Polychromatic418967fa.accept_27_20_12_11_1_7817 20 174 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 227 (accept_3_2 19 174 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 174 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 174 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 174 227 (accept_3_2 16 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 174 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 174 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 227 (accept_3_2 13 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 227 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 174 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 174 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 174 227 (accept_3_2 10 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  174 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 174 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 227 (accept_3_2 7 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 174 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 174 227 (accept_3_2 4 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  174 227 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 174 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 174 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 227 (accept_3_2 1 174 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 174 227)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 173 227
  (Eq.refl Bool.true) (allA_succ_of_accept 54 173 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 173 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 227
  (Polychromatic418967fa.accept_19_15_2_18_1_6699 53 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 173 227 (accept_3_2 52 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 173 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 173 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 173 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 227 (accept_3_2 49 173 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 227 (Polychromatic418967fa.accept_11_4_8_7_1_819
  48 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 227
  (Polychromatic418967fa.accept_16_15_13_3_1_4215 47 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 173 227 (accept_3_2 46 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 173 227 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 173 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 173 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 227 (accept_3_2 43 173 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 227
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 41 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 227 (accept_3_2 40 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 227 (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 173 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 227 (accept_3_2 37 173 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 173 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 227
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 227 (accept_3_2 34 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 227 (Polychromatic418967fa.accept_13_7_4_6_1_3221 33 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 227 (Polychromatic418967fa.accept_21_11_5_17_1_760 32 173 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 227 (accept_3_2 31 173 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 173 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 227
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 227 (accept_3_2 28 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 227 (Polychromatic418967fa.accept_31_27_18_10_1_13582 27 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 173 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 227 (accept_3_2 25 173 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 227 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 173
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 227 (accept_3_2 22 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 227 (Polychromatic418967fa.accept_15_6_8_2_1_104 21 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 227 (Polychromatic418967fa.accept_13_7_4_6_1_3221 20 173 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 227 (accept_3_2 19 173 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 173 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 227
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 17 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 227 (accept_3_2 16 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 173 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 227 (accept_3_2 13 173 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 227 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 173 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 227
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 227 (accept_3_2 10 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 173 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 227 (accept_3_2 7 173 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 173 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 227
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 227 (accept_3_2 4 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 227 (Polychromatic418967fa.accept_19_3_2_18_1_9566 3 173 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 227 (accept_3_2 1 173 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 227))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 172 227
  (Eq.refl Bool.true) (allA_of_3_0 56 172 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 171 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 56 171 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 227 (accept_3_2 55 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 227 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 171 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 227
  (Polychromatic418967fa.accept_13_1_2_6_1_515 53 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 171 227 (accept_3_2 52 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 171 227 (Polychromatic418967fa.accept_13_12_2_6_1_2396 51 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 171 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 227 (accept_3_2 49 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 227 (Polychromatic418967fa.accept_13_9_2_6_1_514 48 171 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 227
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 47 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 171 227 (accept_3_2 46 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 171 227 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 171 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 227 (accept_3_2 43 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 227 (Polychromatic418967fa.accept_15_12_6_2_1_2760 42 171 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 227
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 41 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 227 (accept_3_2 40 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 171 227 (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 171 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 227 (accept_3_2 37 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 227 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 171 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 227
  (Polychromatic418967fa.accept_13_9_2_6_1_514 35 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 227 (accept_3_2 34 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 227 (accept_3_2 31 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 227 (Polychromatic418967fa.accept_13_4_2_6_1_1043 30 171 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 227
  (Polychromatic418967fa.accept_17_12_1_6_1_3680 29 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 227 (accept_3_2 28 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 227 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 227 (accept_3_2 25 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 227 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 171 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 227
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 227 (accept_3_2 22 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 227 (accept_3_2 19 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 227 (Polychromatic418967fa.accept_20_18_11_7_1_6344 18 171 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 227
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 227 (accept_3_2 16 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 227 (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 227 (accept_3_2 13 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 227 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 171 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 227
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 11 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 227 (accept_3_2 10 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 227 (accept_3_2 7 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 227 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 171 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 227
  (Polychromatic418967fa.accept_17_5_1_6_1_2615 5 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 227 (accept_3_2 4 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 227 (Polychromatic418967fa.accept_17_3_1_6_1_251 3 171 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 227 (accept_3_2 1 171 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 227))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 170 227
  (Eq.refl Bool.true) (allA_succ_of_accept 57 170 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 170 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 170 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 170 227 (accept_3_2 55 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 170 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 170 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 170 227 (accept_3_2 52 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 170 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 170 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 170 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 170 227 (accept_3_2 49 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 170 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 170 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 170 227 (accept_3_2 46 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 170 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 170 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 170 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 170 227 (accept_3_2 43 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 170 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 170 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 170 227 (accept_3_2 40 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 170 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 170 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 170 227
  (Polychromatic418967fa.accept_20_18_10_7_1_9245 38 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 170 227 (accept_3_2 37 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 170 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 170 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 170 227 (Polychromatic418967fa.accept_13_9_1_6_1_510 35 170
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 170 227 (accept_3_2 34 170
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 170 227 (Polychromatic418967fa.accept_4_1_2_3_1_9
  33 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 170 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 170 227 (accept_3_2 31 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 170 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 170 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 170 227 (accept_3_2 28 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 170 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 170 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 170 227 (accept_3_2 25 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 170 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 170 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 227 (accept_3_2 22 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 170 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 170 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 170 227
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 170 227 (accept_3_2 19 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 170 227 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 170 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 227 (accept_3_2 16 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 170 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 170 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 170 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 170 227 (accept_3_2 13 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 170 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 170 227 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 170 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 227 (accept_3_2 10 170 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 170 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 170 227 (accept_3_2 7 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  170 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 170 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 227 (accept_3_2 4 170 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 170 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 227
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 2 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 227 (accept_3_2 1 170 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 169 227 (Eq.refl Bool.true) (allA_of_3_0
  59 169 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 168 227 (Eq.refl Bool.true) (allA_succ_of_accept 59
  168 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 168 227 (accept_3_2 58 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 168 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 168 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 168 227 (Polychromatic418967fa.accept_23_10_7_20_1_5208 56 168
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 168 227 (accept_3_2 55 168
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 168 227
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 168 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 168 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 168 227 (accept_3_2 52 168 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 168 227 (Polychromatic418967fa.accept_18_15_6_11_1_5651 51 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 168 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 168 227 (accept_3_2 49 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 168 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 168 227 (Polychromatic418967fa.accept_19_9_16_18_1_3887 47 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 168 227 (accept_3_2 46 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 168 227 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 168
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 168 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 168 227 (accept_3_2 43 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 168 227 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 168 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 168 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 168 227 (accept_3_2 40 168 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 168 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 168 227
  (Polychromatic418967fa.accept_22_16_14_7_1_13581 38 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 168 227 (accept_3_2 37 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 168 227 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 168 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 168 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 168 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 227 (accept_3_2 34 168 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 168 227
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 33 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 168 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 168 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 227 (accept_3_2 31 168 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 168 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 168 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 168 227 (Polychromatic418967fa.accept_10_9_8_7_1_714
  29 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 168 227 (accept_3_2 28
  168 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 168 227
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 168 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 168 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 227 (accept_3_2 25 168 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 168 227 (Polychromatic418967fa.accept_25_24_18_2_1_13580 24 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 168 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 227 (accept_3_2 22 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 168 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 168 227 (Polychromatic418967fa.accept_13_7_12_6_1_1039 20 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 227 (accept_3_2 19 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 227 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 168
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 227 (accept_3_2 16 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 168 227 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 168 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 168 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 227 (accept_3_2 13 168 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 227
  (Polychromatic418967fa.accept_16_11_8_3_1_3183 11 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 168 227 (accept_3_2 10 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  168 227 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 168 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 168 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 227 (accept_3_2 7 168 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 168 227 (Polychromatic418967fa.accept_25_6_18_2_1_13579 6 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 227 (accept_3_2 4 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  168 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 168 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 168 227 (Polychromatic418967fa.accept_13_2_12_6_1_2394 2 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 227 (accept_3_2 1 168 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168 227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 167 227 (Eq.refl Bool.true) (allA_succ_of_accept 60 167 227 (Polychromatic418967fa.accept_7_4_6_3_1_271
  60 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 227
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 59 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 167 227 (accept_3_2 58 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 167 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 167 227 (Polychromatic418967fa.accept_13_4_11_6_1_1033 56 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 227 (accept_3_2 55 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 167 227 (Polychromatic418967fa.accept_17_3_14_6_1_3742 54 167
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 167 227 (accept_3_2 52 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 167 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 167 227 (Polychromatic418967fa.accept_18_14_5_11_1_5676 50 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 227 (accept_3_2 49 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 167 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 227
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 47 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 227 (accept_3_2 46 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 227 (Polychromatic418967fa.accept_19_7_15_18_1_8132 45 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 167 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 227 (accept_3_2 43 167 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 227
  (Polychromatic418967fa.accept_16_9_7_3_1_614 41 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 167 227 (accept_3_2 40 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 167 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 167 227 (Polychromatic418967fa.accept_14_10_13_3_1_2552 38 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 227 (accept_3_2 37 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 167 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 227 (accept_3_2 34 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 167 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 227 (accept_3_2 31 167 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 227
  (Polychromatic418967fa.accept_21_8_20_17_1_7455 29 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 167 227 (accept_3_2 28 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 167 227 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 167 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 167 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 227 (accept_3_2 25 167 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 227 (Polychromatic418967fa.accept_9_6_5_2_1_421
  24 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 227 (accept_3_2 22 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 167 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 227 (accept_3_2 19 167 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 227 (accept_3_2 16 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 227 (Polychromatic418967fa.accept_18_14_5_11_1_5676 14 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 227 (accept_3_2 13 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 167 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 227 (accept_3_2 10 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 167 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 227 (accept_3_2 7 167 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 167 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 227
  (Polychromatic418967fa.accept_13_5_11_6_1_505 5 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 227 (accept_3_2 4 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 167 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 167 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 227 (accept_3_2 1 167 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 166
  227 (Eq.refl Bool.true) (allA_of_3_0 62 166 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 165 227
  (Eq.refl Bool.true) (allA_succ_of_accept 62 165 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 227 (accept_3_2 61 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 165 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 227 (accept_3_2 58 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 165 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 165 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 227 (accept_3_2 55 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 227 (accept_3_2 52 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 165 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 165 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 227 (accept_3_2 49 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 227
  (Polychromatic418967fa.accept_19_9_13_18_1_10812 47 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 165 227 (accept_3_2 46 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 165 227 (Polychromatic418967fa.accept_17_11_12_6_1_6070 45 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 44
  165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 227 (accept_3_2 43
  165 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 165 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 165 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 227 (accept_3_2 40 165 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 165 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 227 (accept_3_2 37 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 165 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 165 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 227 (accept_3_2 34 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 227 (accept_3_2 31 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 165 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 165 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 227 (accept_3_2 28 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 227 (accept_3_2 25 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 165 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 165 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 227 (accept_3_2 22 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 227 (Polychromatic418967fa.accept_14_7_11_3_1_5365 21 165 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 165 227 (accept_3_2 19 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 165 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 165 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 227 (accept_3_2 16 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 227 (accept_3_2 13 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 165 227 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 165 227 (Polychromatic418967fa.accept_17_11_12_6_1_6070 11 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 227 (accept_3_2 10 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 227 (Polychromatic418967fa.accept_19_9_13_18_1_10812 9 165
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 227 (accept_3_2 7 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  165 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 165 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 227 (accept_3_2 4 165 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 227 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 165 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 227 (accept_3_2 1 165 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 164 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 164 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 164 227 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 164
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 164 227 (accept_3_2 61 164
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 164 227
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 60 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 164 227 (Polychromatic418967fa.accept_22_15_10_7_1_13578 59 164 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 164 227 (accept_3_2 58 164 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 164 227
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 56 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 164 227 (accept_3_2 55 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 164 227 (Polychromatic418967fa.accept_13_2_8_6_1_2390 54 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 164 227 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 164 227 (accept_3_2 52 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 164 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 164 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 164 227 (accept_3_2 49 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 164 227 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 164 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 164 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 164 227 (accept_3_2 46 164 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 164 227
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 44 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 164 227 (accept_3_2 43 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 164 227 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 164 227 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 164 227 (accept_3_2 40 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 164 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 164 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 164 227 (accept_3_2 37 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 164 227 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 164 227 (Polychromatic418967fa.accept_14_7_10_3_1_1034 35 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 164 227 (accept_3_2 34 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 164 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 164 227
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 164 227 (accept_3_2 31 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 164 227 (Polychromatic418967fa.accept_17_13_11_6_1_4837 30 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 164 227 (Polychromatic418967fa.accept_17_12_11_6_1_3729 29 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 164 227 (accept_3_2 28 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 164 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 164 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 164 227 (accept_3_2 25 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 164 227 (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 164 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 164 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 164 227 (accept_3_2 22 164 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 164 227
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 164 227 (accept_3_2 19 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 164 227 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 164 227 (Polychromatic418967fa.accept_16_1_4_3_1_3148 17 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 227 (accept_3_2 16 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 164 227
  (Polychromatic418967fa.accept_11_3_10_7_1_129 14 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 164 227 (accept_3_2 13 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 164 227 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 164 227 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 227 (accept_3_2 10 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 227
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 8 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 227 (accept_3_2 7 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 227 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 227 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 227 (accept_3_2 4 164 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 227
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 227 (accept_3_2 1 164 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 163 227 (Eq.refl Bool.true)
  (allA_of_3_0 65 163 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 162 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 162 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 162 227 (accept_3_2 64 162 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 162 227 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 162 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 162 227
  (Polychromatic418967fa.accept_19_5_10_18_1_2705 62 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 162 227 (accept_3_2 61 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 162 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 162 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 162 227 (Polychromatic418967fa.accept_10_9_2_7_1_1096 59 162
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 162 227 (accept_3_2 58 162
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9
  57 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 162 227
  (Polychromatic418967fa.accept_21_14_15_17_1_2972 56 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 162 227 (accept_3_2 55 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 162 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 162 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 162 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 162 227 (accept_3_2 52 162 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 162 227 (Polychromatic418967fa.accept_7_2_1_3_1_102
  51 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 227
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 50 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 162 227 (accept_3_2 49 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 162 227 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 162 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 162 227 (accept_3_2 46 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 162 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 162 227 (accept_3_2 43 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 162 227 (Polychromatic418967fa.accept_17_8_9_6_1_7330 42 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 227 (accept_3_2 40 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 162 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 162 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 227
  (Polychromatic418967fa.accept_16_6_2_3_1_4223 38 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 162 227 (accept_3_2 37 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 162 227 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 162 227 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 162 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 162 227 (accept_3_2 34 162 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 162 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 227
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 162 227 (accept_3_2 31 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 162 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 227 (accept_3_2 28 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 162 227 (Polychromatic418967fa.accept_19_8_10_18_1_5232 27 162 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 227
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 162 227 (accept_3_2 25 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 162 227 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 162 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 162 227 (accept_3_2 22 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 162 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 227
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 162 227 (accept_3_2 19 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 162 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 227 (accept_3_2 16 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 162 227 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 162 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 227
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 162 227 (accept_3_2 13 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 162 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 162 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 227 (accept_3_2 10 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 227
  (Polychromatic418967fa.accept_17_8_9_6_1_7330 8 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 162 227 (accept_3_2 7 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  162 227 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 162 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 227 (accept_3_2 4 162 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 162 227 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 162 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 162 227 (accept_3_2 1 162 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 161 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 161 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 161 227 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 161
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 227 (accept_3_2 64 161
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 227
  (Polychromatic418967fa.accept_13_11_5_6_1_519 63 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 161 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 161 227 (accept_3_2 61 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 161 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 161 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 161 227 (Polychromatic418967fa.accept_9_5_8_2_1_409
  59 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 227 (accept_3_2 58
  161 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 227
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 161 227 (Polychromatic418967fa.accept_10_6_1_7_1_342 56 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 161 227 (accept_3_2 55 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 161 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 161 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 161 227 (Polychromatic418967fa.accept_13_1_5_6_1_1048
  53 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 227 (accept_3_2 52
  161 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 227
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 161 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 161 227 (accept_3_2 49 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 161 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 161 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 227
  (Polychromatic418967fa.accept_21_5_14_17_1_10616 47 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 161 227 (accept_3_2 46 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 161 227 (Polychromatic418967fa.accept_16_13_1_3_1_2205 45 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 227 (Polychromatic418967fa.accept_10_4_1_7_1_371 44 161
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 227 (accept_3_2 43 161
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 161 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 161 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 227 (accept_3_2 40 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 161 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 161 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 227 (accept_3_2 37
  161 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 227
  (Polychromatic418967fa.accept_10_6_1_7_1_342 36 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 161 227 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 227 (accept_3_2 34 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 161 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 161 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 227 (Polychromatic418967fa.accept_9_5_8_2_1_409
  32 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 227 (accept_3_2 31
  161 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 161 227 (Polychromatic418967fa.accept_13_3_5_6_1_3192 29 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 227 (accept_3_2 28 161 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 161 227 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 161 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 227 (accept_3_2 25 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 161 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 227 (accept_3_2 22 161 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 161 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 227
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 227 (accept_3_2 19 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 227 (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 161 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 227 (accept_3_2 16 161 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 161 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 227 (accept_3_2 13 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 227 (Polychromatic418967fa.accept_13_11_5_6_1_519 11 161 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 227 (accept_3_2 10 161 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 227 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 161
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 227
  (Polychromatic418967fa.accept_19_8_9_18_1_2704 8 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 227 (accept_3_2 7 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 161 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 227 (accept_3_2 4 161 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 161 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 227 (accept_3_2 1 161 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 160 227 (Eq.refl Bool.true)
  (allA_of_3_0 68 160 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 159 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 159 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 227 (accept_3_2 67 159 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 159 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 159 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 65
  159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 227 (accept_3_2 64
  159 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 227
  (Polychromatic418967fa.accept_18_9_15_11_1_5693 63 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 227 (accept_3_2 61 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 159 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 159 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 159 227 (accept_3_2 58 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 159 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 227 (accept_3_2 55 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 227 (Polychromatic418967fa.accept_14_12_5_3_1_1011 54 159 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 227 (accept_3_2 52 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 159 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 227 (accept_3_2 49 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 159 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 227
  (Polychromatic418967fa.accept_21_5_12_17_1_10634 47 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 159 227 (accept_3_2 46 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 159 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 159 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 159 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 227 (accept_3_2 43 159 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 227 (Polychromatic418967fa.accept_10_2_9_7_1_720
  42 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 227 (accept_3_2 40 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 159 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 227 (accept_3_2 37 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 159 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 227 (accept_3_2 34 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 227 (accept_3_2 31 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 159 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 227
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 227 (accept_3_2 28 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 227 (Polychromatic418967fa.accept_13_1_3_6_1_158 27 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 227 (accept_3_2 25 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 227 (Polychromatic418967fa.accept_18_6_15_11_1_3141 24 159 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 227 (accept_3_2 22 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 227 (accept_3_2 19 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 227 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 159 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 227 (accept_3_2 16 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 227 (accept_3_2 13 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 159 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 227
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 227 (accept_3_2 10 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 227 (accept_3_2 7 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 227 (Polychromatic418967fa.accept_18_6_15_11_1_3141 6 159 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 227 (accept_3_2 4 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 159 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 227 (accept_3_2 1 159 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 158 227 (Eq.refl Bool.true) (allA_succ_of_accept 69 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9
  69 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 158 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 158 227 (accept_3_2 67 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 158 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 158 227 (accept_3_2 64 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 158 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 158 227
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 158 227 (accept_3_2 61 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 158 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 158 227 (Polychromatic418967fa.accept_10_9_8_7_1_714 59 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 158 227 (accept_3_2 58 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 158 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 158 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 158 227 (accept_3_2 55 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 158 227 (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 158 227 (accept_3_2 52 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 158 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 158 227
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 158 227 (accept_3_2 49 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 158 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 158 227 (Polychromatic418967fa.accept_11_3_4_7_1_114 47 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 158 227 (accept_3_2 46 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 158 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 158 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 158 227 (accept_3_2 43 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 158 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 158 227 (accept_3_2 40 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 158 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 158 227
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 38 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 158 227 (accept_3_2 37 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 158 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 158 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 158 227 (accept_3_2 34 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 158 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 158 227 (accept_3_2 31 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 158 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 227 (accept_3_2 28 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 158 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 158 227 (accept_3_2 25 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 158 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 158 227 (Polychromatic418967fa.accept_13_10_2_6_1_1044 23 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 227 (accept_3_2 22 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 227
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 158 227 (accept_3_2 19 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 158 227 (Polychromatic418967fa.accept_17_1_5_6_1_3717 18 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 227 (accept_3_2 16 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 158 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 227
  (Polychromatic418967fa.accept_11_3_4_7_1_114 14 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 158 227 (accept_3_2 13 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 158 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 158 227 (Polychromatic418967fa.accept_16_11_14_3_1_3140 11 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 227 (accept_3_2 10 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 227
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 227 (accept_3_2 7 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 227 (accept_3_2 4 158 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 158 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 227
  (Polychromatic418967fa.accept_18_2_14_11_1_3139 2 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 227 (accept_3_2 1 158 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 157 227 (Eq.refl Bool.true)
  (allA_of_3_0 71 157 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 156 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 156 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 156 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 156 227 (accept_3_2 70 156 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 156 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 156 227 (Polychromatic418967fa.accept_7_5_2_3_1_106
  68 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 156 227 (accept_3_2 67
  156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 156 227
  (Polychromatic418967fa.accept_20_6_16_7_1_9232 66 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 156 227 (Polychromatic418967fa.accept_17_14_3_6_1_3716 65 156 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 156 227 (accept_3_2 64 156 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 156 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 156 227 (Polychromatic418967fa.accept_7_6_2_3_1_107
  62 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 227 (accept_3_2 61
  156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 156 227
  (Polychromatic418967fa.accept_9_6_3_2_1_431 60 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 156 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 156 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 156 227 (accept_3_2 58 156 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 156 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 156 227
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 56 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 156 227 (accept_3_2 55 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 156 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 156 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 156 227 (accept_3_2 52 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 156 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 156 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 156 227 (accept_3_2 49 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 156 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 156 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 156 227 (accept_3_2 46 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 156 227 (Polychromatic418967fa.accept_18_9_12_11_1_5642 45 156 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 156 227 (accept_3_2 43 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 156 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 156 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 156 227 (accept_3_2 40 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 156 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 156 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 227
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 156 227 (accept_3_2 37 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 156 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 156 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 227 (accept_3_2 34 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 156 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 156 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 156 227 (accept_3_2 31 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 156 227 (Polychromatic418967fa.accept_19_11_4_18_1_5226 30 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 156 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 227 (accept_3_2 28 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 156 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 156 227 (accept_3_2 25 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 156 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 156 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 227 (accept_3_2 22 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 156 227 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 156 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 227
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 156 227 (accept_3_2 19 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 156 227 (Polychromatic418967fa.accept_17_1_3_6_1_3672 18 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 156 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 227 (accept_3_2 16 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 156 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 156 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 156 227 (accept_3_2 13 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 156 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 156 227 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 156 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 227 (accept_3_2 10 156 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 156 227 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 156 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 156 227 (accept_3_2 7 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  156 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 156 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 227 (accept_3_2 4 156 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 156 227 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 156 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 227
  (Polychromatic418967fa.accept_19_2_4_18_1_9556 2 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 156 227 (accept_3_2 1 156 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 155 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 155 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 155 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 227 (Polychromatic418967fa.accept_15_11_5_2_1_520 71 155
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 227 (accept_3_2 70 155
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 155 227
  (Polychromatic418967fa.accept_17_1_2_6_1_818 69 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 155 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 155 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 227 (accept_3_2 67 155 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 155 227 (Polychromatic418967fa.accept_19_9_3_18_1_5263 66 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 155 227 (accept_3_2 64 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 155 227 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 155 227 (Polychromatic418967fa.accept_10_2_5_7_1_1124 62 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 227 (accept_3_2 61 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 155 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 227
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 59 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 227 (accept_3_2 58 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 227 (Polychromatic418967fa.accept_13_5_12_6_1_508 57 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 227 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 227 (accept_3_2 55 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 155 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 227
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 227 (accept_3_2 52 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 227 (Polychromatic418967fa.accept_11_6_1_7_1_1315 50 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 227 (accept_3_2 49 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 227 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 155
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 227
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 227 (accept_3_2 46 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 227 (Polychromatic418967fa.accept_20_5_15_7_1_7869 45 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 155 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 227 (accept_3_2 43 155 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 227 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 227
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 41 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 227 (accept_3_2 40 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 227 (Polychromatic418967fa.accept_10_8_5_7_1_358 38 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 227 (accept_3_2 37 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 227 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 155
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 227
  (Polychromatic418967fa.accept_17_1_2_6_1_818 35 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 227 (accept_3_2 34 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 155 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 227 (accept_3_2 31 155 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 227
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 227 (accept_3_2 28 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 227 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 155 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 227 (accept_3_2 25 155 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 227 (Polychromatic418967fa.accept_16_8_11_3_1_4279 24 155 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 227 (accept_3_2 22 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 227 (Polychromatic418967fa.accept_17_4_2_6_1_2629 21 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 227 (Polychromatic418967fa.accept_13_7_12_6_1_1039 20 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 227 (accept_3_2 19 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 155 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 227
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 227 (accept_3_2 16 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 227 (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 227 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 227 (accept_3_2 13 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 155 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 227
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 227 (accept_3_2 10 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 227 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 155 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 227 (accept_3_2 7 155 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 227 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 155 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 227
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 227 (accept_3_2 4 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 227 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 155 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 155 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 227 (accept_3_2 1 155 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 74 154 227 (Eq.refl Bool.true) (allA_of_3_0 74 154 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 75 153 227 (Eq.refl Bool.true) (allA_succ_of_accept 74 153 227 (Polychromatic418967fa.accept_4_2_1_3_1_27
  74 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 227 (accept_3_2 73
  153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 153 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 153 227 (Polychromatic418967fa.accept_16_7_9_3_1_1324 71 153 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 227 (accept_3_2 70 153 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 153 227 (Polychromatic418967fa.accept_11_3_10_7_1_129 69 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 153 227 (accept_3_2 67 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 153 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 153 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 153 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 227 (accept_3_2 64 153 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 227 (accept_3_2 61 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 153 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 227 (Polychromatic418967fa.accept_15_14_3_2_1_2811 59 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 227 (accept_3_2 58 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 227 (Polychromatic418967fa.accept_13_5_10_6_1_2361 57 153
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 227 (accept_3_2 55 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 153 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 227 (accept_3_2 52 153 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 227 (accept_3_2 49 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 153 227 (Polychromatic418967fa.accept_13_9_10_6_1_1028 48 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 227 (Polychromatic418967fa.accept_11_3_10_7_1_129 47 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 227 (accept_3_2 46 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 227 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 153
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 227 (accept_3_2 43 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 153 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 153 227 (Polychromatic418967fa.accept_13_2_10_6_1_1676 41 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 227 (accept_3_2 40 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 153 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 153 227 (accept_3_2 37 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 153 227 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 153 227 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 227 (accept_3_2 34 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 227 (Polychromatic418967fa.accept_18_15_9_11_1_4371 33 153
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 227 (accept_3_2 31 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 153 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 153 227 (Polychromatic418967fa.accept_13_3_10_6_1_2382 29 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 227 (accept_3_2 28 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 153
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 227 (accept_3_2 25 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 153 227 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 153 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 227 (accept_3_2 22 153 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 227 (Polychromatic418967fa.accept_19_2_1_18_1_2660 21 153 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 227 (accept_3_2 19 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 153 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 153 227 (Polychromatic418967fa.accept_13_4_10_6_1_989 17 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 227 (accept_3_2 16 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 227 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 153
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 227 (accept_3_2 13 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 227 (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 153 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 227 (accept_3_2 10 153 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 227 (accept_3_2 7 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 227 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 153 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 227 (accept_3_2 4 153 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 227 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 153 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 227 (accept_3_2 1 153 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 152 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 152 227 (Polychromatic418967fa.accept_10_4_2_7_1_373
  74 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 152 227 (accept_3_2 73
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 152 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 152 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 152 227 (accept_3_2 70 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 152 227 (Polychromatic418967fa.accept_9_5_8_2_1_409
  68 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 152 227 (accept_3_2 67
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 152 227
  (Polychromatic418967fa.accept_9_3_8_2_1_162 66 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 152 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 152 227 (accept_3_2 64 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 152 227 (Polychromatic418967fa.accept_12_2_8_11_1_31
  62 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 152 227 (accept_3_2 61
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 152 227
  (Polychromatic418967fa.accept_9_6_8_2_1_410 60 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 152 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 152 227 (accept_3_2 58 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 152 227 (Polychromatic418967fa.accept_13_4_9_6_1_2376
  56 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 152 227 (accept_3_2 55
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 152 227
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 152 227 (Polychromatic418967fa.accept_13_1_9_6_1_146 53 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 152 227 (accept_3_2 52 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 152 227 (Polychromatic418967fa.accept_7_1_5_3_1_268
  50 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 152 227 (accept_3_2 49
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 152 227
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 152 227 (Polychromatic418967fa.accept_14_5_12_3_1_3397 47 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 152 227 (accept_3_2 46 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 152 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 44
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 152 227 (accept_3_2 43
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 152 227
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 152 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 227 (accept_3_2 40 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 227 (Polychromatic418967fa.accept_11_5_9_7_1_411
  38 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 152 227 (accept_3_2 37
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 152 227
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 152 227 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 227 (accept_3_2 34 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 227 (Polychromatic418967fa.accept_9_5_8_2_1_409
  32 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 152 227 (accept_3_2 31
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 152 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 152 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 227 (accept_3_2 28 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 227 (Polychromatic418967fa.accept_12_2_8_11_1_31
  26 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 152 227 (accept_3_2 25
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 152 227
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 152 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 227 (accept_3_2 22 152 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 227 (Polychromatic418967fa.accept_13_7_9_6_1_148
  20 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 227 (accept_3_2 19
  152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 152 227
  (Polychromatic418967fa.accept_24_18_8_11_1_10125 18 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 152 227 (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 152 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 227 (accept_3_2 16 152 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 227 (accept_3_2 13 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 227 (Polychromatic418967fa.accept_16_11_8_3_1_3183 11 152 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 227 (accept_3_2 10 152 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 227
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 227 (accept_3_2 7 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 227 (accept_3_2 4 152 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 227 (accept_3_2 1 152 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 151 227 (Eq.refl
  Bool.true) (allA_of_3_0 77 151 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 150 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 150 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 150 227 (accept_3_2 76 150 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 150 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 150 227 (Polychromatic418967fa.accept_13_9_7_6_1_1673
  74 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 150 227 (accept_3_2 73
  150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 150 227
  (Polychromatic418967fa.accept_21_9_3_17_1_4365 72 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 150 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 150 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 150 227 (accept_3_2 70 150 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 150 227 (Polychromatic418967fa.accept_9_5_6_2_1_161
  68 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 150 227 (accept_3_2 67
  150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 150 227
  (Polychromatic418967fa.accept_9_3_6_2_1_160 66 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 150 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 150 227 (accept_3_2 64 150 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 150 227 (Polychromatic418967fa.accept_14_7_10_3_1_1034 63 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 150 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 150 227 (accept_3_2 61 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 150 227 (Polychromatic418967fa.accept_21_18_3_17_1_13577 60 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 59 150 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 150 227 (accept_3_2 58 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 150 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 150 227
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 56 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 150 227 (accept_3_2 55 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 150 227 (Polychromatic418967fa.accept_17_3_14_6_1_3742 54 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 227 (accept_3_2 52 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 150 227 (Polychromatic418967fa.accept_13_12_7_6_1_1015 51 150 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 150 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 150 227 (accept_3_2 49 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 150 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 150 227 (Polychromatic418967fa.accept_22_3_18_7_1_10537 47 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 227 (accept_3_2 46 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 150 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 150 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 150 227 (accept_3_2 43 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 150 227 (Polychromatic418967fa.accept_17_8_14_6_1_8727 42 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 150 227 (accept_3_2 40 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 150 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 227
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 38 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 150 227 (accept_3_2 37 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 150 227 (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 150 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 227 (accept_3_2 34 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 227 (accept_3_2 31 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 150 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 227 (accept_3_2 28 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 150 227 (Polychromatic418967fa.accept_13_1_7_6_1_142 27 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 150 227 (accept_3_2 25 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 150 227 (Polychromatic418967fa.accept_17_7_14_6_1_4882 24 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 227 (accept_3_2 22 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 227
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 150 227 (accept_3_2 19 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 150 227 (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 227 (accept_3_2 16 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 150 227 (Polychromatic418967fa.accept_17_15_14_6_1_7354 15 150 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 150 227 (accept_3_2 13 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 150 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 150 227 (Polychromatic418967fa.accept_16_11_6_3_1_6564 11 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 227 (accept_3_2 10 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 227 (accept_3_2 7 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  150 227 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 150 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 227 (accept_3_2 4 150 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 150 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 150 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 227
  (Polychromatic418967fa.accept_16_2_6_3_1_5396 2 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 150 227 (accept_3_2 1 150 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 149 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 149 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 227
  (Polychromatic418967fa.accept_20_17_9_7_1_13576 77 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 149 227 (accept_3_2 76 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 149 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 149 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 149 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 227 (accept_3_2 73 149 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 227 (Polychromatic418967fa.accept_10_2_9_7_1_720
  72 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 149 227 (accept_3_2 70 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 149 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 149 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 227 (accept_3_2 67 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 227
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 227 (accept_3_2 64 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 227 (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 227 (accept_3_2 61 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 227
  (Polychromatic418967fa.accept_19_2_16_18_1_10922 59 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 149 227 (accept_3_2 58 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 149 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 149 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 227 (Polychromatic418967fa.accept_11_1_6_7_1_116 56 149
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 227 (accept_3_2 55 149
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 149 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 149 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 227 (accept_3_2 52 149 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 149 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 227 (accept_3_2 49
  149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 227
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 149 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 149 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 227 (accept_3_2 46 149 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 149 227 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 227 (accept_3_2 43 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 227 (accept_3_2 40 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 227 (accept_3_2 37 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 227 (accept_3_2 34 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 227
  (Polychromatic418967fa.accept_10_2_9_7_1_720 32 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 227 (accept_3_2 31 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 227 (accept_3_2 28 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 227 (accept_3_2 25 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 227 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 227 (accept_3_2 22 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 149 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 227
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 227 (accept_3_2 19 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 227 (accept_3_2 16 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 227 (accept_3_2 13 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 227 (Polychromatic418967fa.accept_17_11_13_6_1_2625 11 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 227 (accept_3_2 10 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 227 (Polychromatic418967fa.accept_19_9_16_18_1_3887 9 149
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 227 (accept_3_2 7 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 227 (accept_3_2 4 149 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 149 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 227 (accept_3_2 1 149 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 148 227 (Eq.refl
  Bool.true) (allA_of_3_0 80 148 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 147 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 80 147 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 147 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 227 (accept_3_2 79 147 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 147 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 227 (Polychromatic418967fa.accept_9_5_3_2_1_171
  77 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 227 (accept_3_2 76
  147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 147 227
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 75 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 147 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 147 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 227 (accept_3_2 73 147 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 147 227 (Polychromatic418967fa.accept_13_7_4_6_1_3221 72 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 227 (accept_3_2 70 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 147 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 147 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 227 (accept_3_2 67 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 227 (Polychromatic418967fa.accept_14_10_7_3_1_1022 66 147 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 227
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 65 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 227 (accept_3_2 64 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 147 227 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 147 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 227 (accept_3_2 61 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 227 (accept_3_2 58 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 147 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 147 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 227 (accept_3_2 55 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 227 (Polychromatic418967fa.accept_13_2_4_6_1_2356 54 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 227 (accept_3_2 52 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 227 (accept_3_2 49 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 227 (Polychromatic418967fa.accept_13_9_4_6_1_1005 48 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 227
  (Polychromatic418967fa.accept_11_3_4_7_1_114 47 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 227 (accept_3_2 46 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 227 (accept_3_2 43 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 227 (accept_3_2 40 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 227 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 227 (accept_3_2 37 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 227 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 227 (accept_3_2 34 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 227 (accept_3_2 31 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 227 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 227
  (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 147 227 (accept_3_2 28 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 147 227 (Polychromatic418967fa.accept_28_27_7_3_1_13575 27 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 26
  147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 227 (accept_3_2 25
  147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 227
  (Polychromatic418967fa.accept_9_6_3_2_1_431 24 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 147 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 227 (accept_3_2 22 147 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 147 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 227 (accept_3_2 19 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 147 227 (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 147 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 227 (accept_3_2 16 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 227 (accept_3_2 13 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 147 227 (Polychromatic418967fa.accept_17_12_11_6_1_3729 12 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 227 (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 227 (accept_3_2 10 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 147
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 227 (accept_3_2 7 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  147 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 147 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 227 (accept_3_2 4 147 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 227 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 147 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 227
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 227 (accept_3_2 1 147 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 146 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 146 227 (Polychromatic418967fa.accept_12_8_2_11_1_246
  80 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 146 227 (accept_3_2 79
  146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 146 227
  (Polychromatic418967fa.accept_23_9_8_20_1_13574 78 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 146 227 (accept_3_2 76 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 146 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 146 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 74 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 146 227 (accept_3_2 73 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 146 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 146 227 (Polychromatic418967fa.accept_10_1_6_7_1_710 71 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 146 227 (accept_3_2 70 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 146 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 146 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 146 227 (accept_3_2 67 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 146 227 (Polychromatic418967fa.accept_13_1_3_6_1_158 66 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 146 227 (accept_3_2 64 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 146 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 146 227
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 62 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 146 227 (accept_3_2 61 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 146 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 146 227 (Polychromatic418967fa.accept_11_4_3_7_1_828 59 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 146 227 (accept_3_2 58 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 146 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 146 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 146 227 (accept_3_2 55 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 146 227 (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 146 227 (accept_3_2 52 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 146 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 146 227
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 50 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 146 227 (accept_3_2 49 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 146 227 (Polychromatic418967fa.accept_11_4_3_7_1_828 48 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 146 227 (Polychromatic418967fa.accept_16_15_2_3_1_4262 47 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 146 227 (accept_3_2 46 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 146 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 146 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 146 227 (accept_3_2 43 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 227 (Polychromatic418967fa.accept_22_20_14_7_1_13573 42 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 227 (accept_3_2 40 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 146 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 227
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 146 227 (accept_3_2 37 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 146 227 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 146 227 (Polychromatic418967fa.accept_13_9_3_6_1_1661 35 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 227 (accept_3_2 34 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 146 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 227 (accept_3_2 31 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 227 (accept_3_2 28 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 227
  (Polychromatic418967fa.accept_11_4_3_7_1_828 26 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 146 227 (accept_3_2 25 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 146 227 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 146 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 227 (accept_3_2 22 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 146 227 (accept_3_2 19 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 146 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 227 (accept_3_2 16 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 227
  (Polychromatic418967fa.accept_13_1_3_6_1_158 14 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 146 227 (accept_3_2 13 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 146 227 (Polychromatic418967fa.accept_17_12_10_6_1_3691 12 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 146 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 227 (accept_3_2 10 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 227 (accept_3_2 7 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 227 (Polychromatic418967fa.accept_15_6_11_2_1_2801 6 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 227 (accept_3_2 4 146 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 146 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 227 (accept_3_2 1 146 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 145 227 (Eq.refl
  Bool.true) (allA_of_3_0 83 145 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 144 227 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 144 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 144 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 144 227 (accept_3_2 82 144 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 144 227 (Polychromatic418967fa.accept_10_1_4_7_1_374 81 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 144 227
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 80 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 144 227 (accept_3_2 79 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 144 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 144 227 (Polychromatic418967fa.accept_14_7_4_3_1_488 77 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 144 227 (accept_3_2 76 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 144 227 (Polychromatic418967fa.accept_27_21_9_11_1_11679 75
  144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 144 227
  (Polychromatic418967fa.accept_13_9_1_6_1_510 74 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 144 227 (accept_3_2 73 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 144 227 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 144 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 144 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 144 227 (accept_3_2 70 144 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 144 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 144 227
  (Polychromatic418967fa.accept_13_3_1_6_1_509 68 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 144 227 (accept_3_2 67 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 144 227 (Polychromatic418967fa.accept_17_15_8_6_1_8733 66 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 144 227 (Polychromatic418967fa.accept_17_14_8_6_1_2643 65 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 144 227 (accept_3_2 64 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 144 227 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 144
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 227
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 144 227 (accept_3_2 61 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 144 227 (Polychromatic418967fa.accept_13_8_1_6_1_997 60 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 144 227 (Polychromatic418967fa.accept_13_7_1_6_1_3287 59 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 144 227 (accept_3_2 58 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 144 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 144 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 227
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 56 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 144 227 (accept_3_2 55 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 144 227 (Polychromatic418967fa.accept_13_2_1_6_1_2365 54 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 144 227 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 227 (accept_3_2 52 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 227 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 144
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 227
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 144 227 (accept_3_2 49 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 144 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 144 227 (Polychromatic418967fa.accept_13_8_1_6_1_997 47 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 227 (accept_3_2 46 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 144 227 (Polychromatic418967fa.accept_19_7_11_18_1_6680 45 144
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 227
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 44 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 144 227 (accept_3_2 43 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 144 227 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 144 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 144 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 227 (accept_3_2 40 144 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 227 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 227
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 38 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 144 227 (accept_3_2 37 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 144 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 144 227 (Polychromatic418967fa.accept_13_9_1_6_1_510 35 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 227 (accept_3_2 34 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 227 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 144
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 227
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 144 227 (accept_3_2 31 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 144 227 (Polychromatic418967fa.accept_21_9_18_17_1_7454 30 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 144 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 144 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 227 (accept_3_2 28 144 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 227
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 144 227 (accept_3_2 25 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 144 227 (Polychromatic418967fa.accept_21_3_18_17_1_12031 24 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 227 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 227 (accept_3_2 22 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 227 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 144
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 227
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 144 227 (accept_3_2 19 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 144 227 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 144 227 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 227 (accept_3_2 16 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 144 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 227
  (Polychromatic418967fa.accept_17_14_8_6_1_2643 14 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 144 227 (accept_3_2 13 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 144 227 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 144 227 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 227 (accept_3_2 10 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 227 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 144 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 227
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 144 227 (accept_3_2 7 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  144 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 144 227 (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 144 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 227 (accept_3_2 4 144 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 227 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 144 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 227
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 144 227 (accept_3_2 1 144 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 143 227
  (Eq.refl Bool.true) (allA_succ_of_accept 84 143 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 227
  (Polychromatic418967fa.accept_19_7_10_18_1_6695 83 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 143 227 (accept_3_2 82 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 143 227 (Polychromatic418967fa.accept_15_6_8_2_1_104 81 143 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 143 227 (Polychromatic418967fa.accept_25_5_18_2_1_13572 80 143
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 227 (accept_3_2 79 143
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 227
  (Polychromatic418967fa.accept_9_6_8_2_1_410 78 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 143 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 143 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 227 (accept_3_2 76 143 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 143 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 143 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 227 (Polychromatic418967fa.accept_10_4_3_7_1_1110
  74 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 227 (accept_3_2 73
  143 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 227
  (Polychromatic418967fa.accept_22_6_11_7_1_13571 72 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 143 227 (Polychromatic418967fa.accept_16_7_15_3_1_1302 71 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 227 (accept_3_2 70 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 143 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 227
  (Polychromatic418967fa.accept_8_4_7_3_1_144 68 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 143 227 (accept_3_2 67 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 143 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 143 227 (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 227 (accept_3_2 64 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 227 (Polychromatic418967fa.accept_23_17_5_20_1_13570 63
  143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 227
  (Polychromatic418967fa.accept_19_5_10_18_1_2705 62 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 143 227 (accept_3_2 61 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 143 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 143 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 143 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 227 (accept_3_2 58 143 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 227 (Polychromatic418967fa.accept_9_3_8_2_1_162
  57 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 227
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 56 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 227 (accept_3_2 55 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 227 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 143 227 (Polychromatic418967fa.accept_24_5_23_11_1_10119 53 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 227 (accept_3_2 52 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 143 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 227 (accept_3_2 49 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 227 (Polychromatic418967fa.accept_17_13_7_6_1_827 47 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 227 (accept_3_2 46 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 227 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 143
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 227
  (Polychromatic418967fa.accept_8_4_7_3_1_144 44 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 227 (accept_3_2 43 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 143 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 227 (accept_3_2 40 143 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 227
  (Polychromatic418967fa.accept_18_2_17_11_1_3178 38 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 143 227 (accept_3_2 37 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 143 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 143 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 227 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 143
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 227 (accept_3_2 34 143
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 227
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 143 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 143 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 227 (accept_3_2 31 143 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 143 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 143 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 227
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 29 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 143 227 (accept_3_2 28 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 143 227 (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 143 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 227 (Polychromatic418967fa.accept_10_6_3_7_1_2197
  26 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 227 (accept_3_2 25
  143 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 227
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 143 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 143 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 227 (accept_3_2 22 143 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 143 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 143 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 227 (Polychromatic418967fa.accept_8_4_7_3_1_144
  20 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 227 (accept_3_2 19
  143 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 227
  (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 143 227 (Polychromatic418967fa.accept_19_17_10_18_1_9563 17 143 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 227 (accept_3_2 16 143 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 227 (accept_3_2 13 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 227 (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 227 (accept_3_2 10 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 227 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 143 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 227
  (Polychromatic418967fa.accept_19_8_10_18_1_5232 8 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 227 (accept_3_2 7 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 143 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 227 (accept_3_2 4 143 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 143 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 227
  (Polychromatic418967fa.accept_16_2_15_3_1_1300 2 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 227 (accept_3_2 1 143 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 142 227
  (Eq.refl Bool.true) (allA_of_3_0 86 142 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 141 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 86 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 227 (accept_3_2 85 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 141 227
  (Polychromatic418967fa.accept_13_5_11_6_1_505 83 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 141 227 (accept_3_2 82 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 141 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 141 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 227 (accept_3_2 79 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 227 (accept_3_2 76 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 141 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 227 (accept_3_2 73 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 141 227 (accept_3_2 70 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 141 227 (Polychromatic418967fa.accept_13_4_11_6_1_1033 69 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 141 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 227 (accept_3_2 67 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 227 (accept_3_2 64 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 141 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 227 (accept_3_2 61 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 227 (accept_3_2 58 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 141 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 141 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 227 (accept_3_2 55 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 227
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 227 (accept_3_2 52 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 141 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 227 (accept_3_2 49 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 227
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 227 (accept_3_2 46 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 227 (Polychromatic418967fa.accept_17_11_5_6_1_4928 45 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 227 (accept_3_2 43 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 227 (accept_3_2 40 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 227 (accept_3_2 37 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 227 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 227 (accept_3_2 34 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 227 (accept_3_2 31 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 227
  (Polychromatic418967fa.accept_19_10_8_18_1_2669 29 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 141 227 (accept_3_2 28 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 141 227 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 141 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 227 (accept_3_2 25 141 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 227 (Polychromatic418967fa.accept_10_4_1_7_1_371
  24 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 227 (accept_3_2 22 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 227 (accept_3_2 19 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 227 (accept_3_2 16 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 227 (accept_3_2 13 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 227
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 227 (accept_3_2 10 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 227 (accept_3_2 7 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 227
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 227 (accept_3_2 4 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 141 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 227 (accept_3_2 1 141 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 140 227
  (Eq.refl Bool.true) (allA_succ_of_accept 87 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 140 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 86 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 140 227 (accept_3_2 85 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 140 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 140 227 (Polychromatic418967fa.accept_13_5_10_6_1_2361 83 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 140 227 (accept_3_2 82 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 140 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 140 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 80 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 140 227 (accept_3_2 79 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 140 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 140 227 (Polychromatic418967fa.accept_13_12_10_6_1_3212 77 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 140 227 (accept_3_2 76 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 140 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 140 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 140 227 (accept_3_2 73 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 140 227 (Polychromatic418967fa.accept_15_12_5_2_1_2786 72 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 140 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 71 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 140 227 (accept_3_2 70 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 140 227
  (Polychromatic418967fa.accept_13_3_10_6_1_2382 68 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 140 227 (accept_3_2 67 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 140 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 140 227 (Polychromatic418967fa.accept_19_8_7_18_1_1595 65 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 140 227 (accept_3_2 64 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 140 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 140 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 140 227 (accept_3_2 61 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 140 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 140 227 (Polychromatic418967fa.accept_11_4_8_7_1_819 59 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 140 227 (accept_3_2 58 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 140 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 140 227
  (Polychromatic418967fa.accept_13_4_10_6_1_989 56 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 140 227 (accept_3_2 55 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 140 227 (Polychromatic418967fa.accept_13_2_10_6_1_1676 54 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 140 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 140 227 (accept_3_2 52 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 140 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 140 227 (accept_3_2 49 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 140 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 140 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 227 (accept_3_2 46 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 140 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 140 227 (accept_3_2 43 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 140 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 140 227 (Polychromatic418967fa.accept_13_2_10_6_1_1676 41 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 140 227 (accept_3_2 40 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 140 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 140 227 (accept_3_2 37 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 140 227 (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 140 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 140 227 (accept_3_2 34 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 227
  (Polychromatic418967fa.accept_22_10_8_7_1_11977 32 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 140 227 (accept_3_2 31 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 140 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 140 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 140 227 (Polychromatic418967fa.accept_13_3_10_6_1_2382 29 140
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 227 (accept_3_2 28 140
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 227
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 140 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 140 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 140 227 (accept_3_2 25 140 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 140 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 140 227 (Polychromatic418967fa.accept_8_7_4_3_1_156
  23 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 227 (accept_3_2 22
  140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 227
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 140 227 (Polychromatic418967fa.accept_16_4_12_3_1_2180 20 140 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 140 227 (accept_3_2 19 140 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 140 227 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 140 227 (accept_3_2 16 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 140 227 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 140 227 (accept_3_2 13 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 140 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 227
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 140 227 (accept_3_2 10 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 140 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 227 (accept_3_2 7 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 140 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 140 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 140 227
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 5 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 140 227 (accept_3_2 4 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  140 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 140 227 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 227 (accept_3_2 1 140 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 140
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 139 227
  (Eq.refl Bool.true) (allA_of_3_0 89 139 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 138 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 138 227 (accept_3_2 88 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 138 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 138 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 86 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 138 227 (accept_3_2 85 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 138 227 (Polychromatic418967fa.accept_22_18_6_7_1_11959 84 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 138 227 (Polychromatic418967fa.accept_25_8_13_2_1_13569 83 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 138 227 (accept_3_2 82 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 138 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 138 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 80 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 138 227 (accept_3_2 79 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 138 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 138 227 (accept_3_2 76 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 138 227 (Polychromatic418967fa.accept_10_5_8_7_1_2174 75 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 138 227
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 74 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 138 227 (accept_3_2 73 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 138 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 138 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 138 227 (accept_3_2 70 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 138 227 (accept_3_2 67 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 138 227 (Polychromatic418967fa.accept_13_1_8_6_1_1016 66 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 138 227 (accept_3_2 64 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 138 227 (Polychromatic418967fa.accept_13_11_8_6_1_1023 63 138 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 138 227 (accept_3_2 61 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 138 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 138 227 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 227 (accept_3_2 58 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 227
  (Polychromatic418967fa.accept_11_1_6_7_1_116 56 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 138 227 (accept_3_2 55 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 138 227 (Polychromatic418967fa.accept_13_2_8_6_1_2390 54 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 227 (accept_3_2 52 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 138 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 227
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 138 227 (accept_3_2 49 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 138 227 (Polychromatic418967fa.accept_19_10_5_18_1_10817 48 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 47 138 227 (Polychromatic418967fa.accept_14_5_12_3_1_3397 47 138 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 227 (accept_3_2 46 138 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 138 227 (accept_3_2 43 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 138 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 227 (accept_3_2 40 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 227 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 227
  (Polychromatic418967fa.accept_17_4_2_6_1_2629 38 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 138 227 (accept_3_2 37 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 138 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 138 227 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 227 (accept_3_2 34 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 138 227 (accept_3_2 31 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 138 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 227 (accept_3_2 28 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 227 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 227 (accept_3_2 25 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 138 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 138 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 227 (accept_3_2 22 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 227
  (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 138 227 (accept_3_2 19 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 138 227 (Polychromatic418967fa.accept_17_1_2_6_1_818 18 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 227 (accept_3_2 16 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 227 (accept_3_2 13 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 138 227 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 227 (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 227 (accept_3_2 10 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 227
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 227 (accept_3_2 7 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  138 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 138 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 227 (accept_3_2 4 138 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 227 (Polychromatic418967fa.accept_21_3_12_17_1_7471 3 138 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 227 (accept_3_2 1 138 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 137 227
  (Eq.refl Bool.true) (allA_succ_of_accept 90 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 137 227
  (Polychromatic418967fa.accept_20_9_17_7_1_4748 89 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 137 227 (accept_3_2 88 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 137 227 (Polychromatic418967fa.accept_13_9_7_6_1_1673 87 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 137 227 (accept_3_2 85 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 137 227 (Polychromatic418967fa.accept_19_8_4_18_1_5283 84 137 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 227
  (Polychromatic418967fa.accept_7_6_4_3_1_266 83 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 137 227 (accept_3_2 82 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 137 227 (Polychromatic418967fa.accept_19_5_4_18_1_5242 81 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 137 227 (Polychromatic418967fa.accept_17_12_1_6_1_3680 80 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 227 (accept_3_2 79 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 137 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 227
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 77 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 137 227 (accept_3_2 76 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 137 227 (Polychromatic418967fa.accept_11_9_5_7_1_815 75 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 227 (accept_3_2 73 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 227 (Polychromatic418967fa.accept_19_15_4_18_1_5227 72 137 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 227
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 137 227 (accept_3_2 70 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 137 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 137 227 (Polychromatic418967fa.accept_19_11_4_18_1_5226 68 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 227 (accept_3_2 67 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 137 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 227
  (Polychromatic418967fa.accept_19_8_4_18_1_5283 65 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 137 227 (accept_3_2 64 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 137 227 (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 227 (accept_3_2 61 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 227 (Polychromatic418967fa.accept_16_12_9_3_1_5363 60 137 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 227
  (Polychromatic418967fa.accept_19_2_4_18_1_9556 59 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 137 227 (accept_3_2 58 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 227 (Polychromatic418967fa.accept_13_4_7_6_1_2359 56 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 227 (accept_3_2 55 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 137 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 227
  (Polychromatic418967fa.accept_11_9_5_7_1_815 53 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 227 (accept_3_2 52 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 227 (Polychromatic418967fa.accept_13_12_7_6_1_1015 51 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 227 (accept_3_2 49 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 227
  (Polychromatic418967fa.accept_21_5_11_17_1_10652 47 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 137 227 (accept_3_2 46 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 137 227 (Polychromatic418967fa.accept_27_18_2_11_1_7797 45 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 227
  (Polychromatic418967fa.accept_16_12_9_3_1_5363 44 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 227 (accept_3_2 43 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 227 (accept_3_2 40 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 227 (Polychromatic418967fa.accept_16_7_9_3_1_1324 39 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 227 (accept_3_2 37 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 227 (Polychromatic418967fa.accept_13_9_7_6_1_1673 35 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 227 (accept_3_2 34 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 227 (Polychromatic418967fa.accept_19_14_4_18_1_6665 33 137
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 227
  (Polychromatic418967fa.accept_20_12_17_7_1_4786 32 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 137 227 (accept_3_2 31 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 137 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 227 (accept_3_2 28 137 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 227 (Polychromatic418967fa.accept_7_6_4_3_1_266
  27 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 227 (accept_3_2 25 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 227 (Polychromatic418967fa.accept_19_5_4_18_1_5242 24 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 227 (Polychromatic418967fa.accept_16_7_9_3_1_1324 23 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 227 (accept_3_2 22 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 227 (Polychromatic418967fa.accept_14_7_11_3_1_5365 21 137
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 227
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 227 (accept_3_2 19 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 227 (Polychromatic418967fa.accept_13_4_7_6_1_2359 17 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 227 (accept_3_2 16 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 137 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 227 (accept_3_2 13 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 227 (Polychromatic418967fa.accept_13_12_7_6_1_1015 12 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 227 (Polychromatic418967fa.accept_19_11_4_18_1_5226 11 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 227 (accept_3_2 10 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 227 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 137 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 227
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 227 (accept_3_2 7 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 227 (Polychromatic418967fa.accept_17_5_1_6_1_2615 5 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 227 (accept_3_2 4 137 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 227 (Polychromatic418967fa.accept_17_3_1_6_1_251 3 137 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 227
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 227 (accept_3_2 1 137 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 136 227
  (Eq.refl Bool.true) (allA_of_3_0 92 136 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 135 227 (Eq.refl
  Bool.true) (allA_succ_of_accept 92 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 227 (accept_3_2 91 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 135 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 89 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 135 227 (accept_3_2 88 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 135 227 (Polychromatic418967fa.accept_11_10_3_7_1_2564 87 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 227 (accept_3_2 85 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 227
  (Polychromatic418967fa.accept_7_6_2_3_1_107 83 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 227 (accept_3_2 82 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 135 227 (Polychromatic418967fa.accept_11_4_3_7_1_828 81 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 227 (accept_3_2 79 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 227
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 77 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 227 (accept_3_2 76 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 135 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 227 (accept_3_2 73 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 227 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 135 227 (accept_3_2 70 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 135 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 227 (accept_3_2 67 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 227 (Polychromatic418967fa.accept_13_1_5_6_1_1048 66 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 227
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 65 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 135 227 (accept_3_2 64 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 135 227 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 227 (accept_3_2 61 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 227 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 227
  (Polychromatic418967fa.accept_11_4_3_7_1_828 59 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 227 (accept_3_2 58 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 227 (accept_3_2 55 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 227
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 227 (accept_3_2 52 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 227 (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 227 (accept_3_2 49 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 227 (accept_3_2 46 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 135 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 227 (accept_3_2 43 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 227 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 227
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 227 (accept_3_2 40 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 227 (Polychromatic418967fa.accept_19_1_2_18_1_10827 39 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 227 (accept_3_2 37 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 227
  (Polychromatic418967fa.accept_19_16_2_18_1_8136 35 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 135 227 (accept_3_2 34 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 135 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 135 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 227 (accept_3_2 31 135 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 227 (Polychromatic418967fa.accept_13_4_5_6_1_3201
  30 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 227 (accept_3_2 28 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 227 (accept_3_2 25 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 227 (Polychromatic418967fa.accept_13_11_5_6_1_519 24 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 227
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 227 (accept_3_2 22 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 227 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 227 (accept_3_2 19 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 227 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 227
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 227 (accept_3_2 16 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 227 (accept_3_2 13 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 227
  (Polychromatic418967fa.accept_13_11_5_6_1_519 11 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 227 (accept_3_2 10 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 227 (accept_3_2 7 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 135 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 227 (accept_3_2 4 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 227 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 135 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 227 (accept_3_2 1 135 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 134
  227 (Eq.refl Bool.true) (allA_succ_of_accept 93 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 134 227
  (Polychromatic418967fa.accept_10_2_4_7_1_352 92 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 134 227 (accept_3_2 91 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 134 227 (Polychromatic418967fa.accept_19_14_1_18_1_5280 90 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 134 227 (accept_3_2 88 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 134 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 134 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 134 227 (accept_3_2 85 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 134 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 134 227 (Polychromatic418967fa.accept_10_3_4_7_1_353 83 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 134 227 (accept_3_2 82 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 134 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 134 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 134 227 (accept_3_2 79 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 134 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 134 227 (accept_3_2 76 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 134 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 134 227
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 134 227 (accept_3_2 73 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 134 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 134 227 (Polychromatic418967fa.accept_10_1_4_7_1_374 71 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 134 227 (accept_3_2 70 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 134 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 134 227
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 134 227 (accept_3_2 67 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 134 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 134 227 (accept_3_2 64 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 134 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 134 227
  (Polychromatic418967fa.accept_10_2_4_7_1_352 62 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 134 227 (accept_3_2 61 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 134 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 134 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 134 227 (accept_3_2 58 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 134 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 134 227 (accept_3_2 55 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 134 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 134 227 (accept_3_2 52 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 134 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 134 227 (accept_3_2 49 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 134 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 134 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 227 (accept_3_2 46 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 227 (accept_3_2 43 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 227 (accept_3_2 40 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 227
  (Polychromatic418967fa.accept_23_15_19_20_1_13568 38 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 134 227 (accept_3_2 37 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 134 227 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 134 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 134 227 (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 134
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 227 (accept_3_2 34 134
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9
  33 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 227
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 227 (accept_3_2 31 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 227 (accept_3_2 28 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 227
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 134 227 (accept_3_2 25 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 134 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 134 227 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 227 (accept_3_2 22 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 227
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 227 (accept_3_2 19 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 227 (accept_3_2 16 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 134 227 (accept_3_2 13 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 134 227 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 134 227 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 227 (accept_3_2 10 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 227
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 227 (accept_3_2 7 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 227 (accept_3_2 4 134 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 134 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 227
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 227 (accept_3_2 1 134 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 133
  227 (Eq.refl Bool.true) (allA_of_3_0 95 133 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 132 227
  (Eq.refl Bool.true) (allA_succ_of_accept 95 132 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 95 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 132 227 (accept_3_2 94 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 132 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 132 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 132 227
  (Polychromatic418967fa.accept_13_1_2_6_1_515 92 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 132 227 (accept_3_2 91 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 132 227 (Polychromatic418967fa.accept_13_12_2_6_1_2396 90 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 132 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 89 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 132 227 (accept_3_2 88 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 132 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 87 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 132 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 86 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 132 227 (accept_3_2 85 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 132 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 132 227 (Polychromatic418967fa.accept_23_14_17_20_1_8624 83 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 132 227 (accept_3_2 82 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 132 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 132 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 132 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 80 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 132 227 (accept_3_2 79 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 132 227 (Polychromatic418967fa.accept_15_3_12_2_1_507 78 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 132 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 132 227 (accept_3_2 76 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 132 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 132 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 74 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 132 227 (accept_3_2 73 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 132 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 132 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 71 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 227 (accept_3_2 70 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 132 227 (Polychromatic418967fa.accept_10_9_2_7_1_1096 69 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 132 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 132 227 (accept_3_2 67 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 132 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 132 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 227 (accept_3_2 64 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 132 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 132 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 132 227 (accept_3_2 61 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 132 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 132 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 227 (accept_3_2 58 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 227
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 56 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 132 227 (accept_3_2 55 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 132 227 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 132 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 227 (accept_3_2 52 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 132 227 (accept_3_2 49 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 132 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 132 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 227 (accept_3_2 46 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 227 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 132 227 (accept_3_2 43 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 132 227 (Polychromatic418967fa.accept_20_2_12_7_1_4799 42 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 132 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 227 (accept_3_2 40 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 227
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 38 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 227 (accept_3_2 37 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 132 227 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 227 (accept_3_2 34 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 227 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 132 227 (accept_3_2 31 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 132 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 132 227 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 227 (accept_3_2 28 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 227 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 132
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 227 (accept_3_2 25 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 227 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 227 (accept_3_2 22 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 227
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 227 (accept_3_2 19 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 132 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 227 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 227 (accept_3_2 16 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 227 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 227 (accept_3_2 13 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 132 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 132 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 227 (accept_3_2 10 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 227 (accept_3_2 7 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 227 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 227 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 227 (accept_3_2 4 132 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 132 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 227 (accept_3_2 1 132 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 131
  227 (Eq.refl Bool.true) (allA_succ_of_accept 96 131 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 131 227
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 95 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 131 227 (accept_3_2 94 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 131 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 131 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 92 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 131 227 (accept_3_2 91 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 131 227 (Polychromatic418967fa.accept_20_10_11_7_1_4796 90 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 89 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 131 227 (accept_3_2 88 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 131 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 87 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 131 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 86 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 227 (accept_3_2 85 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 131 227
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 83 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 131 227 (accept_3_2 82 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 131 227 (Polychromatic418967fa.accept_13_3_1_6_1_509 81 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 131 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 227 (accept_3_2 79 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 227
  (Polychromatic418967fa.accept_19_1_17_18_1_8101 77 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 131 227 (accept_3_2 76 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 131 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 131 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 227 (Polychromatic418967fa.accept_10_4_1_7_1_371 74 131
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 227 (accept_3_2 73 131
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 131 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 131 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 227 (accept_3_2 70 131 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 131 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 227 (Polychromatic418967fa.accept_13_3_1_6_1_509
  68 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 227 (accept_3_2 67
  131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 227
  (Polychromatic418967fa.accept_9_3_5_2_1_28 66 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 131 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 131 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 227 (accept_3_2 64 131 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 131 227 (Polychromatic418967fa.accept_19_6_17_18_1_8117 63 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 227 (accept_3_2 61 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 227 (Polychromatic418967fa.accept_13_7_1_6_1_3287 59 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 227 (accept_3_2 58 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 227
  (Polychromatic418967fa.accept_10_6_1_7_1_342 56 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 227 (accept_3_2 55 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 227 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 227 (accept_3_2 52 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 227
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 227 (accept_3_2 49 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 227 (Polychromatic418967fa.accept_11_3_10_7_1_129 47 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 227 (accept_3_2 46 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 227 (Polychromatic418967fa.accept_17_11_12_6_1_6070 45 131
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 227 (accept_3_2 43 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 227 (Polychromatic418967fa.accept_13_2_1_6_1_2365 41 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 227 (accept_3_2 40 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 227
  (Polychromatic418967fa.accept_20_18_11_7_1_6344 38 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 131 227 (accept_3_2 37 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 131 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 131 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 227 (accept_3_2 34 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 227 (Polychromatic418967fa.accept_9_6_5_2_1_421
  33 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 227
  (Polychromatic418967fa.accept_18_14_5_11_1_5676 32 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 131 227 (accept_3_2 31 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 131 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 131 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 227 (accept_3_2 28 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 227
  (Polychromatic418967fa.accept_17_10_12_6_1_4917 27 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 227 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 227 (accept_3_2 25 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 227
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 227 (accept_3_2 22 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 227 (Polychromatic418967fa.accept_13_7_1_6_1_3287 20 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 227 (accept_3_2 19 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 227 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 131
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 227
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 227 (accept_3_2 16 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 227 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 227 (accept_3_2 13 131 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 227
  (Polychromatic418967fa.accept_17_11_12_6_1_6070 11 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 131 227 (accept_3_2 10 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 131 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 131 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 227 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 227 (accept_3_2 7 131 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 227 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 227
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 227 (accept_3_2 4 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 227 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 131 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 227 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 227 (accept_3_2 1 131 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  130 227 (Eq.refl Bool.true) (allA_of_3_0 98 130 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 129 227
  (Eq.refl Bool.true) (allA_succ_of_accept 98 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 227 (accept_3_2 97 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 129 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 95 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 129 227 (accept_3_2 94 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 129 227 (Polychromatic418967fa.accept_13_2_12_6_1_2394 93 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 129 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 227 (accept_3_2 91 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 89 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 129 227 (accept_3_2 88 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 129 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 227 (accept_3_2 85 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 227 (Polychromatic418967fa.accept_16_4_1_3_1_6581 84 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 227
  (Polychromatic418967fa.accept_13_5_12_6_1_508 83 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 129 227 (accept_3_2 82 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 129 227 (Polychromatic418967fa.accept_11_4_8_7_1_819 81 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 129 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 227 (accept_3_2 79 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 227 (accept_3_2 76 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 129 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 227 (accept_3_2 73 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 227 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 227 (accept_3_2 70 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 129 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 129 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 227 (accept_3_2 67 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 227
  (Polychromatic418967fa.accept_20_5_9_7_1_10766 65 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 227 (accept_3_2 64 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 129 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 227 (accept_3_2 61 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 129 227 (accept_3_2 58 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 129 227 (Polychromatic418967fa.accept_13_5_12_6_1_508 57 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 129 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 227 (accept_3_2 55 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 227 (accept_3_2 52 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 227 (accept_3_2 49 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 227 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 227
  (Polychromatic418967fa.accept_19_9_15_18_1_10919 47 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 129 227 (accept_3_2 46 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 129 227 (Polychromatic418967fa.accept_16_13_1_3_1_2205 45 129 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 227 (accept_3_2 43 129 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 227 (accept_3_2 40 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 227 (accept_3_2 37 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 227 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 129 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 227 (accept_3_2 34 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 227 (accept_3_2 31 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 227
  (Polychromatic418967fa.accept_16_13_1_3_1_2205 29 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 227 (accept_3_2 28 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 227 (accept_3_2 25 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 227 (accept_3_2 22 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 227 (Polychromatic418967fa.accept_17_4_10_6_1_4869 21 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 227 (accept_3_2 19 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 227
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 227 (accept_3_2 16 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 227 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 227 (accept_3_2 13 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 227 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 227
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 227 (accept_3_2 10 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 227 (Polychromatic418967fa.accept_19_9_15_18_1_10919 9 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 227 (accept_3_2 7 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 227
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 227 (accept_3_2 4 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 227 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 129 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 227 (accept_3_2 1 129 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  128 227 (Eq.refl Bool.true) (allA_succ_of_accept 99 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 128 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 98 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 128 227 (accept_3_2 97 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 128 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 128 227 (Polychromatic418967fa.accept_10_5_8_7_1_2174 95 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 128 227 (accept_3_2 94 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 128 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 92 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 128 227 (accept_3_2 91 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 128 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 128 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 128 227 (accept_3_2 88 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 128 227
  (Polychromatic418967fa.accept_12_2_8_11_1_31 86 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 128 227 (accept_3_2 85 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 128 227 (Polychromatic418967fa.accept_15_9_8_2_1_1109 84 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 128 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 128 227 (accept_3_2 82 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 128 227
  (Polychromatic418967fa.accept_19_4_14_18_1_5234 80 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 128 227 (accept_3_2 79 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 128 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 128 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 128 227 (Polychromatic418967fa.accept_19_1_14_18_1_3919 77 128
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 128 227 (accept_3_2 76 128
  227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 128 227
  (Polychromatic418967fa.accept_6_3_2_5_1_32 75 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 128 227 (Polychromatic418967fa.accept_12_2_8_11_1_31 74 128 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 128 227 (accept_3_2 73 128 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 128 227 (Polychromatic418967fa.accept_19_15_14_18_1_6696 72 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 128 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 128 227 (accept_3_2 70 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 128 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 128 227 (accept_3_2 67 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 128 227 (Polychromatic418967fa.accept_15_6_8_2_1_104 66 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 128 227
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 65 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 128 227 (accept_3_2 64 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 128 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 128 227 (accept_3_2 61 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 128 227 (Polychromatic418967fa.accept_13_8_11_6_1_1035 60 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 128 227
  (Polychromatic418967fa.accept_10_9_8_7_1_714 59 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 128 227 (accept_3_2 58 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 128 227 (Polychromatic418967fa.accept_13_4_11_6_1_1033 56 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 128 227 (accept_3_2 55 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 128 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 227
  (Polychromatic418967fa.accept_18_17_2_11_1_9749 53 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 128 227 (accept_3_2 52 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 128 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 128 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 128 227 (accept_3_2 49 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 128 227 (Polychromatic418967fa.accept_7_6_2_3_1_107
  48 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 128 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 128 227 (accept_3_2 46 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 128 227 (Polychromatic418967fa.accept_13_5_11_6_1_505 44 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 227 (accept_3_2 43 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 128 227 (Polychromatic418967fa.accept_17_8_9_6_1_7330 42 128
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 227
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 128 227 (accept_3_2 40 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 128 227 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 227 (accept_3_2 37 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 128 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 227
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 227 (accept_3_2 34 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 227 (Polychromatic418967fa.accept_17_15_9_6_1_8705 32 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 227 (accept_3_2 31 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 227 (Polychromatic418967fa.accept_13_4_11_6_1_1033 30 128
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 227
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 128 227 (accept_3_2 28 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 128 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 227 (accept_3_2 25 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 227 (Polychromatic418967fa.accept_15_9_8_2_1_1109 24 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 227
  (Polychromatic418967fa.accept_19_4_14_18_1_5234 23 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 128 227 (accept_3_2 22 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 227 (accept_3_2 19 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 227 (Polychromatic418967fa.accept_13_5_11_6_1_505
  18 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 227
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 17 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 128 227 (accept_3_2 16 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 128 227 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 227 (accept_3_2 13 128 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 227 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 227
  (Polychromatic418967fa.accept_21_11_2_17_1_2975 11 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 128 227 (accept_3_2 10 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 227 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 227 (accept_3_2 7 128 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 227 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 227
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 227 (accept_3_2 4 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 227 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 227 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 227 (accept_3_2 1 128 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 127 227 (Eq.refl Bool.true) (allA_of_3_0 101 127 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 126
  227 (Eq.refl Bool.true) (allA_succ_of_accept 101 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 126 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 126 227 (accept_3_2 100 126 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 126 227
  (Polychromatic418967fa.accept_17_14_7_6_1_11222 99 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 126 227 (Polychromatic418967fa.accept_13_7_9_6_1_148 98 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 126 227 (accept_3_2 97 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 126 227 (Polychromatic418967fa.accept_19_1_12_18_1_10820 96
  126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 126 227
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 95 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 126 227 (accept_3_2 94 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 126 227 (Polychromatic418967fa.accept_13_1_9_6_1_146 92 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 126 227 (accept_3_2 91 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 126 227 (Polychromatic418967fa.accept_24_18_6_11_1_10090 90
  126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 126 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 126 227 (accept_3_2 88 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 126 227 (Polychromatic418967fa.accept_15_12_6_2_1_2760 87 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 126 227 (Polychromatic418967fa.accept_11_9_5_7_1_815 86 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 126 227 (accept_3_2 85 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 126 227 (Polychromatic418967fa.accept_17_16_7_6_1_7343 84 126
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 126 227
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 83 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 126 227 (accept_3_2 82 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 126 227 (Polychromatic418967fa.accept_13_2_9_6_1_501 80 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 126 227 (accept_3_2 79 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 126 227 (Polychromatic418967fa.accept_22_12_16_7_1_13527 78
  126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 126 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 126 227 (accept_3_2 76 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 126 227 (Polychromatic418967fa.accept_11_9_5_7_1_815 75 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 126 227 (Polychromatic418967fa.accept_19_17_12_18_1_5248 74 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 126 227 (accept_3_2 73 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 126 227 (Polychromatic418967fa.accept_13_7_9_6_1_148 72 126
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 126 227
  (Polychromatic418967fa.accept_10_1_6_7_1_710 71 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 126 227 (accept_3_2 70 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 126 227 (Polychromatic418967fa.accept_13_3_9_6_1_502 68 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 227 (accept_3_2 67 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 126 227 (Polychromatic418967fa.accept_13_1_9_6_1_146 66 126
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 126 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 126 227 (accept_3_2 64 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 126 227 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 126 227 (Polychromatic418967fa.accept_13_10_9_6_1_1026 62 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 126 227 (accept_3_2 61 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 126 227 (Polychromatic418967fa.accept_23_14_11_20_1_11929 60
  126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 126 227
  (Polychromatic418967fa.accept_13_7_9_6_1_148 59 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 126 227 (accept_3_2 58 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 126 227 (Polychromatic418967fa.accept_13_4_9_6_1_2376 56 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 126 227 (accept_3_2 55 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 126 227 (Polychromatic418967fa.accept_13_2_9_6_1_501 54 126
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 126 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 126 227 (accept_3_2 52 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 126 227 (Polychromatic418967fa.accept_10_1_6_7_1_710 51 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 126 227 (Polychromatic418967fa.accept_17_16_7_6_1_7343 50 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 126 227 (accept_3_2 49 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 126 227 (Polychromatic418967fa.accept_17_14_7_6_1_11222 48 126
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 227
  (Polychromatic418967fa.accept_17_13_7_6_1_827 47 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 126 227 (accept_3_2 46 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 126 227 (Polychromatic418967fa.accept_19_6_12_18_1_8141 44 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 227 (accept_3_2 43 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 126 227 (Polychromatic418967fa.accept_11_9_5_7_1_815 42 126
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 227
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 126 227 (accept_3_2 40 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 126 227 (Polychromatic418967fa.accept_19_1_12_18_1_10820 39 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 227 (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 227 (accept_3_2 37 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 126 227 (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 126
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 227
  (Polychromatic418967fa.accept_22_13_16_7_1_7160 35 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 126 227 (accept_3_2 34 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 126 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 227 (Polychromatic418967fa.accept_19_13_12_18_1_2677 32
  126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 227 (accept_3_2 31
  126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 227
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 126 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 227 (accept_3_2 28 126 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 126 227 (Polychromatic418967fa.accept_13_1_9_6_1_146 27 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 227
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 126 227 (accept_3_2 25 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 126 227 (Polychromatic418967fa.accept_25_24_1_2_1_11793 24 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 126 227 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 227 (accept_3_2 22 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 227
  (Polychromatic418967fa.accept_11_9_5_7_1_815 20 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 227 (accept_3_2 19 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 126 227 (Polychromatic418967fa.accept_24_18_6_11_1_10090 18 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 227 (accept_3_2 16 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 227 (Polychromatic418967fa.accept_13_2_9_6_1_501 15 126
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 227
  (Polychromatic418967fa.accept_13_1_9_6_1_146 14 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 227 (accept_3_2 13 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 126 227 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 227 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 227 (accept_3_2 10 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 227
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 126 227 (accept_3_2 7 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  126 227 (Polychromatic418967fa.accept_19_6_12_18_1_8141 6 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 126 227 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 227 (accept_3_2 4 126 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 227 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 126 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 227
  (Polychromatic418967fa.accept_13_2_9_6_1_501 2 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 227 (accept_3_2 1 126 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 125 227 (Eq.refl Bool.true) (allA_succ_of_accept 102 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 125
  227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 125 227
  (Polychromatic418967fa.accept_15_11_5_2_1_520 101 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 125 227 (accept_3_2 100 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 125 227 (Polychromatic418967fa.accept_19_4_11_18_1_3909 99 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 227 (accept_3_2 97 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 125 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 125 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 95 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 125 227 (accept_3_2 94 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 125 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 125 227 (Polychromatic418967fa.accept_10_2_5_7_1_1124 92 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 227 (accept_3_2 91 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 125 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 125 227
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 89 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 125 227 (accept_3_2 88 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 125 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 87 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 125 227 (accept_3_2 85 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 125 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 227
  (Polychromatic418967fa.accept_10_3_5_7_1_330 83 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 125 227 (accept_3_2 82 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 125 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 125 227 (Polychromatic418967fa.accept_11_3_4_7_1_114 80 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 125 227 (accept_3_2 79 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 125 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 227 (accept_3_2 76 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 125 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 227 (accept_3_2 73 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 125 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 227
  (Polychromatic418967fa.accept_15_11_5_2_1_520 71 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 125 227 (accept_3_2 70 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 125 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 125 227 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 227 (accept_3_2 67 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 125 227 (accept_3_2 64 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 125 227 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 227 (accept_3_2 61 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 125 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 227 (accept_3_2 58 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 227 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 227 (accept_3_2 55 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 125 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 227 (accept_3_2 52 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 227 (accept_3_2 49 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 227
  (Polychromatic418967fa.accept_11_3_4_7_1_114 47 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 227 (accept_3_2 46 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 227 (Polychromatic418967fa.accept_19_7_11_18_1_6680 45 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 227 (accept_3_2 43 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 227 (accept_3_2 40 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 227 (accept_3_2 37 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 227 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 227
  (Polychromatic418967fa.accept_20_15_5_7_1_4791 35 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 227 (accept_3_2 34 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 227 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 227 (accept_3_2 31 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 227
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 227 (accept_3_2 28 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 227 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 227 (accept_3_2 25 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 227
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 227 (accept_3_2 22 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 227 (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 227 (accept_3_2 19 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 227
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 17 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 227 (accept_3_2 16 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 227 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 227 (accept_3_2 13 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 227
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 227 (accept_3_2 10 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 227 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 227 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 227 (accept_3_2 7 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 227
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 227 (accept_3_2 4 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 227 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 125 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 227 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 227 (accept_3_2 1 125 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125
  227))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 124 227 (Eq.refl Bool.true) (allA_of_3_0 104 124 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 123
  227 (Eq.refl Bool.true) (allA_succ_of_accept 104 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 123 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 227 (accept_3_2 103 123 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 227 (Polychromatic418967fa.accept_9_3_6_2_1_160
  102 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 227
  (Polychromatic418967fa.accept_19_6_9_18_1_8140 101 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 123 227 (accept_3_2 100 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 123 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 123 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 123 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 227 (accept_3_2 97 123 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 227 (Polychromatic418967fa.accept_10_6_3_7_1_2197
  96 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 95 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 123 227 (accept_3_2 94 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 123 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 227 (accept_3_2 91 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 89 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 227 (accept_3_2 88 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 123 227 (Polychromatic418967fa.accept_15_12_3_2_1_2756 87 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 227 (accept_3_2 85 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 227
  (Polychromatic418967fa.accept_7_6_4_3_1_266 83 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 227 (accept_3_2 82 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 123 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 227 (accept_3_2 79 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 227 (accept_3_2 76 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 123 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 227 (accept_3_2 73 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 227 (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 123 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 227
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 123 227 (accept_3_2 70 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 123 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 227 (accept_3_2 67 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 227
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 227 (accept_3_2 64 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 123 227 (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 227 (accept_3_2 61 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 227 (Polychromatic418967fa.accept_18_6_15_11_1_3141 60 123 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 227 (accept_3_2 58 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 227 (accept_3_2 55 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 227 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 227 (accept_3_2 52 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 227 (Polychromatic418967fa.accept_19_13_9_18_1_10939 51 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 227 (accept_3_2 49 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 123 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 227
  (Polychromatic418967fa.accept_16_15_11_3_1_2179 47 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 123 227 (accept_3_2 46 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 123 227 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 123 227 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 123 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 227 (accept_3_2 43 123 227
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 227 (Polychromatic418967fa.accept_11_9_2_7_1_1298
  42 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 227
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 227 (accept_3_2 40 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 227 (accept_3_2 37 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 227 (accept_3_2 34 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 227 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 227 (accept_3_2 31 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 227
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 227 (accept_3_2 28 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 227 (accept_3_2 25 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 227 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 227 (accept_3_2 22 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 227 (accept_3_2 19 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 227 (Polychromatic418967fa.accept_22_18_13_7_1_11960 18 123 227
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 227
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 227 (accept_3_2 16 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 227 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 227 (accept_3_2 13 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 227
  (Polychromatic418967fa.accept_17_11_4_6_1_2631 11 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 227 (accept_3_2 10 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 227 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 227 (accept_3_2 7 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 227 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 123 227 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 227
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 227 (accept_3_2 4 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 227 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 123 227 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 227 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 227 (accept_3_2 1 123 227 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123
  227)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_227_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


