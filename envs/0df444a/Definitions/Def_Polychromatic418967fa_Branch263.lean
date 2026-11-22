-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch263
-- name    : Polychromatic418967fa_Branch263
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:30:32.297181+00:00
-- url     : https://prove2.me/theorems/80c9f133-5f84-444b-b738-e30c5645ae09
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch263_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_263 : allB 263 263 :=
  allB_succ' 2 262 263 (Eq.refl Bool.true) (allA_of_3_0 2 262 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  261 263 (Eq.refl Bool.true) (allA_succ_of_accept 2 261 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 261 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 261 263 (accept_3_2 1 261 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 261 263))) (allB_succ' 4 260 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 260 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 260 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 260 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 260 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 260 263 (accept_3_2 1 260 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 260 263)))) (allB_succ' 5 259 263 (Eq.refl Bool.true) (allA_of_3_0
  5 259 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 258 263 (Eq.refl Bool.true) (allA_succ_of_accept 5
  258 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 258 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 258 263 (accept_3_2 4 258 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 258 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 258 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 258 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 258 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 258 263 (accept_3_2 1 258 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 258 263)))))) (allB_succ' 7 257 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 257 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 257 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 257 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 257 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 257 263 (accept_3_2 4 257 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 257 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  257 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 257 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 257 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 257 263 (accept_3_2 1 257 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 257 263)))))))
  (allB_succ' 8 256 263 (Eq.refl Bool.true) (allA_of_3_0 8 256 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 255 263 (Eq.refl Bool.true) (allA_succ_of_accept 8 255 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 255 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 255 263 (accept_3_2 7 255 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 255 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  255 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 255 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 255 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 255 263 (accept_3_2 4 255 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  255 263 (Polychromatic418967fa.accept_16_3_15_7_1_3417 3 255 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 255 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 255 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 263 (accept_3_2 1 255 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 255 263))))))))) (allB_succ' 10 254 263 (Eq.refl Bool.true) (allA_succ_of_accept 9 254
  263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 254 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 254 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 254 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 254 263 (accept_3_2 7 254 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 254 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 254 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 254 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  254 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 254 263 (accept_3_2 4 254
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 254 263 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 254 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 254 263
  (Polychromatic418967fa.accept_11_2_1_10_1_196 2 254 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 254 263 (accept_3_2 1 254 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 254
  263)))))))))) (allB_succ' 11 253 263 (Eq.refl Bool.true) (allA_of_3_0 11 253 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 252 263 (Eq.refl Bool.true) (allA_succ_of_accept 11 252 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 252 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 252 263 (accept_3_2 10 252 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  252 263 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 252 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 252 263 (Polychromatic418967fa.accept_13_8_5_3_1_427 8 252 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 252 263 (accept_3_2 7 252 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 252 263 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 252 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 252 263
  (Polychromatic418967fa.accept_10_5_2_3_1_239 5 252 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 252 263 (accept_3_2 4 252 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  252 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 252 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 252 263 (Polychromatic418967fa.accept_13_2_5_3_1_406 2 252 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 252 263 (accept_3_2 1 252 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 252 263)))))))))))) (allB_succ' 13 251 263 (Eq.refl Bool.true) (allA_succ_of_accept 12
  251 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 251 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 251 263 (Polychromatic418967fa.accept_19_11_4_16_1_9308 11 251 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 251 263 (accept_3_2 10 251 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 251 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 251 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 251 263
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 251 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 251 263 (accept_3_2 7 251 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  251 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 251 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 251 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 251 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 251 263 (accept_3_2 4 251 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 251 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 251 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 251 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 251 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 251 263 (accept_3_2 1 251 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 251
  263))))))))))))) (allB_succ' 14 250 263 (Eq.refl Bool.true) (allA_of_3_0 14 250 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 249 263 (Eq.refl Bool.true) (allA_succ_of_accept 14 249 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 249 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 249 263 (accept_3_2 13 249 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 249 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 249 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 249 263 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 249 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 249 263 (accept_3_2 10 249 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 249 263 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 249 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 249 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 249 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 249 263 (accept_3_2 7 249 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  249 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 249 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 249 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 249 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 263 (accept_3_2 4 249 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 249 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 249 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 249 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 249 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 249 263 (accept_3_2 1 249 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249
  263))))))))))))))) (allB_succ' 16 248 263 (Eq.refl Bool.true) (allA_succ_of_accept 15 248 263
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 248 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 248 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 248 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 248 263 (accept_3_2 13 248 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 248 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 248 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 248 263 (Polychromatic418967fa.accept_10_1_8_3_1_947
  11 248 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 248 263 (accept_3_2 10
  248 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 248 263
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 248 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 248 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 248 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 248 263 (accept_3_2 7 248 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 248 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 248 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 248 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 5
  248 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 248 263 (accept_3_2 4 248
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 248 263 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 248 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 248 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 248 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 248 263 (accept_3_2 1 248 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248
  263)))))))))))))))) (allB_succ' 17 247 263 (Eq.refl Bool.true) (allA_of_3_0 17 247 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 246 263 (Eq.refl Bool.true) (allA_succ_of_accept 17 246 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 246 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 246 263 (accept_3_2 16 246 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 246 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 246 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 246 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 246 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 246 263 (accept_3_2 13 246 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 246 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 246 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 246 263
  (Polychromatic418967fa.accept_22_11_4_21_1_16104 11 246 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 246 263 (accept_3_2 10 246 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 246 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 246 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 246 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 246 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 246 263 (accept_3_2 7 246 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 246 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 6
  246 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 246 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 246 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 246 263 (accept_3_2 4 246 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  246 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 246 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 246 263 (Polychromatic418967fa.accept_13_2_12_3_1_415 2 246 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 263 (accept_3_2 1 246 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 246 263)))))))))))))))))) (allB_succ' 19 245 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 245 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 245 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 245 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 245
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 245 263 (accept_3_2 16 245
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 245 263
  (Polychromatic418967fa.accept_13_2_11_3_1_873 15 245 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 245 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 245 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 245 263 (accept_3_2 13 245 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 245 263 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 245 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 245 263
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 245 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 245 263 (accept_3_2 10 245 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  245 263 (Polychromatic418967fa.accept_27_9_2_20_1_12263 9 245 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 245 263 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 245 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 263 (accept_3_2 7 245 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 245 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 245 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 245 263
  (Polychromatic418967fa.accept_13_5_11_3_1_902 5 245 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 245 263 (accept_3_2 4 245 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  245 263 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 245 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 245 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 245 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 245 263 (accept_3_2 1 245 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 245 263))))))))))))))))))) (allB_succ' 20 244 263 (Eq.refl Bool.true) (allA_of_3_0 20
  244 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 243 263 (Eq.refl Bool.true) (allA_succ_of_accept 20
  243 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 243 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 243 263 (accept_3_2 19 243 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 243 263 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 243 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 243 263 (Polychromatic418967fa.accept_22_17_1_21_1_6602 17 243
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 263 (accept_3_2 16 243
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 243 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 243 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 243 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 243 263 (accept_3_2 13 243 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 243 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 243 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 243 263 (Polychromatic418967fa.accept_15_11_3_8_1_750
  11 243 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 263 (accept_3_2 10
  243 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 243 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 243 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 243 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 263 (accept_3_2 7 243 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 243 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 243 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 263 (Polychromatic418967fa.accept_13_5_9_3_1_870 5
  243 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 263 (accept_3_2 4 243
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 263
  (Polychromatic418967fa.accept_17_3_5_8_1_1687 3 243 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 243 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 243 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 263 (accept_3_2 1 243 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 243 263))))))))))))))))))))) (allB_succ' 22 242 263 (Eq.refl Bool.true) (allA_succ_of_accept 21
  242 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 242 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 242 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 242 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 242 263 (accept_3_2 19 242 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 242 263 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 242
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 242 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 242 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 242 263 (accept_3_2 16 242 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 242 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 242 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 242 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 242 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 242 263 (accept_3_2 13 242 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 242 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 242 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 242 263
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 242 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 242 263 (accept_3_2 10 242 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  242 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 242 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 242 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 242 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 242 263 (accept_3_2 7 242 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 242 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 242 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 242 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 242 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 242 263 (accept_3_2 4 242 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  242 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 242 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 242 263 (Polychromatic418967fa.accept_19_2_14_16_1_7992 2 242 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 242 263 (accept_3_2 1 242 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 242 263)))))))))))))))))))))) (allB_succ' 23 241 263 (Eq.refl Bool.true)
  (allA_of_3_0 23 241 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 240 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 240 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 240 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 240 263 (accept_3_2 22 240 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 240 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 240 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 240 263 (Polychromatic418967fa.accept_7_6_2_4_1_291
  20 240 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 240 263 (accept_3_2 19
  240 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 240 263
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 240 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 240 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 240 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 240 263 (accept_3_2 16 240 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 240 263 (Polychromatic418967fa.accept_18_15_6_11_1_5651 15 240 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 240 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 240 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 240 263 (accept_3_2 13 240 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 240 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 240 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 240 263 (Polychromatic418967fa.accept_17_11_2_8_1_7569 11 240 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 240 263 (accept_3_2 10 240 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 240 263 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 240 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 240 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 240 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 240 263 (accept_3_2 7 240 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  240 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 240 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 240 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 240 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 240 263 (accept_3_2 4 240 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 240 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 240 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 240 263
  (Polychromatic418967fa.accept_21_2_9_11_1_13096 2 240 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 240 263 (accept_3_2 1 240 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240
  263)))))))))))))))))))))))) (allB_succ' 25 239 263 (Eq.refl Bool.true) (allA_succ_of_accept 24 239 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 239 263 (Polychromatic418967fa.accept_19_4_11_16_1_1474 23 239 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 239 263 (accept_3_2 22 239 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 239 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 239 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 239 263
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 239 263 (accept_3_2 19 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 239 263 (Polychromatic418967fa.accept_14_4_1_11_1_5026 18 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 239 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 239 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 239 263 (accept_3_2 16 239 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 239 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 239 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 239 263
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 239 263 (accept_3_2 13 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 239 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 239 263 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 239 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 239 263 (accept_3_2 10 239 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 239 263 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 239 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 239 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 239 263 (accept_3_2 7 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  239 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 239 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 239 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 263 (accept_3_2 4 239 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 239 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 263
  (Polychromatic418967fa.accept_13_2_5_3_1_406 2 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 239 263 (accept_3_2 1 239 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239
  263))))))))))))))))))))))))) (allB_succ' 26 238 263 (Eq.refl Bool.true) (allA_of_3_0 26 238 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 237 263 (Eq.refl Bool.true) (allA_succ_of_accept 26 237 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 237 263 (accept_3_2 25 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 237 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 237 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 237 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 263 (accept_3_2 22 237 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 263 (Polychromatic418967fa.accept_25_21_12_13_1_16084 21 237 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 237 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 237 263 (accept_3_2 19 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 237 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 237 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 237 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 263 (accept_3_2 16 237 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 237 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 237 263 (accept_3_2 13 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 237 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 237 263 (Polychromatic418967fa.accept_15_11_12_8_1_739 11 237 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 263 (accept_3_2 10 237 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 237 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 263 (accept_3_2 7 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  237 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 237 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 237 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 263 (accept_3_2 4 237 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 237 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 263 (accept_3_2 1 237 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237
  263))))))))))))))))))))))))))) (allB_succ' 28 236 263 (Eq.refl Bool.true) (allA_succ_of_accept 27 236 263
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 236 263 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 236 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 236 263 (accept_3_2 25 236 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 236 263 (Polychromatic418967fa.accept_13_11_2_3_1_883 24 236 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 236 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 236 263 (accept_3_2 22 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 236 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 236 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 236 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 236 263 (accept_3_2 19 236 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 236 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 236 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 236 263
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 236 263 (accept_3_2 16 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 236 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 236 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 236 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 236 263 (accept_3_2 13 236 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 236 263 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 236
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 236 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 236 263 (accept_3_2 10 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  236 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 236 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 236 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 236 263 (accept_3_2 7 236 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 236 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 236 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 236 263
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 236 263 (accept_3_2 4 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  236 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 236 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 236 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 236 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 236 263 (accept_3_2 1 236 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 236 263)))))))))))))))))))))))))))) (allB_succ' 29 235 263 (Eq.refl Bool.true)
  (allA_of_3_0 29 235 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 234 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 234 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 234 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 234 263 (accept_3_2 28 234 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 234 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 234 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 234 263
  (Polychromatic418967fa.accept_19_7_6_16_1_3818 26 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 234 263 (accept_3_2 25 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 234 263 (Polychromatic418967fa.accept_20_4_14_3_1_3181 24 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 234 263 (Polychromatic418967fa.accept_22_1_14_21_1_16045 23 234 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 234 263 (accept_3_2 22 234 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 234 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 234 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 234 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 234 263 (accept_3_2 19 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 234 263 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 234 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 234 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 234 263 (accept_3_2 16 234 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 234 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 234 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 234 263
  (Polychromatic418967fa.accept_15_14_9_8_1_3165 14 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 234 263 (accept_3_2 13 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 234 263 (Polychromatic418967fa.accept_19_12_6_16_1_10731 12 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 263 (Polychromatic418967fa.accept_19_11_6_16_1_3805 11 234 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 263 (accept_3_2 10 234 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 234 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  234 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 234 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 234 263 (accept_3_2 7 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  234 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 234 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 234 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 234 263 (accept_3_2 4 234 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 234 263 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 234 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 234 263
  (Polychromatic418967fa.accept_15_2_9_8_1_736 2 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 234 263 (accept_3_2 1 234 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234
  263)))))))))))))))))))))))))))))) (allB_succ' 31 233 263 (Eq.refl Bool.true) (allA_succ_of_accept 30 233 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 233 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 233 263 (Polychromatic418967fa.accept_16_13_9_7_1_4532 29 233 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 233 263 (accept_3_2 28 233 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 233 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 233 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 233 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  233 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 233 263 (accept_3_2 25
  233 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 233 263
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 233 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 233 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 233 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 233 263 (accept_3_2 22 233 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 233 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 233 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 233 263 (Polychromatic418967fa.accept_7_6_2_4_1_291
  20 233 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 263 (accept_3_2 19
  233 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 233 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 233 263 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 233 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 263 (accept_3_2 16 233 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 233 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 233 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  233 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 263 (accept_3_2 13
  233 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 233 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 233 263 (Polychromatic418967fa.accept_19_11_5_16_1_1456 11 233 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 263 (accept_3_2 10 233 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 263 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 233 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 263
  (Polychromatic418967fa.accept_16_8_9_7_1_768 8 233 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 263 (accept_3_2 7 233 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 233 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 233 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 263 (accept_3_2 4 233 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 233 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 233 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 263 (accept_3_2 1 233 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  263))))))))))))))))))))))))))))))) (allB_succ' 32 232 263 (Eq.refl Bool.true) (allA_of_3_0 32 232 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 231 263 (Eq.refl Bool.true) (allA_succ_of_accept 32 231 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 231 263 (accept_3_2 31 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 231 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 231 263 (Polychromatic418967fa.accept_15_14_6_8_1_1410 29 231 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 263 (accept_3_2 28 231 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 231 263 (Polychromatic418967fa.accept_18_9_15_11_1_5693 27 231
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 231 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 231 263 (accept_3_2 25 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 231 263 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 231 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 231 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 263 (accept_3_2 22 231 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 231 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 263 (accept_3_2 19 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 231 263 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 231 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 231 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 263 (accept_3_2 16 231 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 263 (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 231 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 263 (accept_3_2 13 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 231 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 231 263 (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 231 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 263 (accept_3_2 10 231 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 231
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 263 (accept_3_2 7 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  231 263 (Polychromatic418967fa.accept_13_6_10_3_1_897 6 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 231 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 231 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 263 (accept_3_2 4 231 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 231 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 263 (accept_3_2 1 231 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  263))))))))))))))))))))))))))))))))) (allB_succ' 34 230 263 (Eq.refl Bool.true) (allA_succ_of_accept 33 230 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 230 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 230 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 230 263 (accept_3_2 31 230 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 230 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 230 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 230 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 230 263 (accept_3_2 28
  230 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 230 263
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 230 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 230 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 230 263 (accept_3_2 25 230 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 230 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 230 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 230 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 23
  230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 230 263 (accept_3_2 22
  230 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 230 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 230 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 230 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 230 263 (accept_3_2 19 230 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 230 263 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 230 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 230 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 230 263 (accept_3_2 16 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 230 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 230 263 (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 230 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 230 263 (accept_3_2 13 230 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 230 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 230 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 230 263
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 230 263 (accept_3_2 10 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  230 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 230 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 230 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 230 263 (accept_3_2 7 230 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 230 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 230 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 230 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 230 263 (accept_3_2 4 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  230 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 230 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 230 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 230 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 230 263 (accept_3_2 1 230 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 230 263)))))))))))))))))))))))))))))))))) (allB_succ' 35 229 263 (Eq.refl Bool.true)
  (allA_of_3_0 35 229 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 228 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 228 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 228 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 228 263 (accept_3_2 34 228 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 228 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 228 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 228 263 (Polychromatic418967fa.accept_9_5_3_2_1_171
  32 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 228 263 (accept_3_2 31
  228 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 228 263
  (Polychromatic418967fa.accept_13_4_7_3_1_92 30 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 228 263 (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 228 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 228 263 (accept_3_2 28 228 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 228 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 228 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 228 263 (Polychromatic418967fa.accept_9_8_3_2_1_417
  26 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 228 263 (accept_3_2 25
  228 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 228 263
  (Polychromatic418967fa.accept_9_6_3_2_1_431 24 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 228 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 228 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 228 263 (accept_3_2 22 228 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 228 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 228 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 228 263
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 228 263 (accept_3_2 19 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 228 263 (Polychromatic418967fa.accept_17_1_7_8_1_6347 18 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 228 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 228 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 263 (accept_3_2 16 228 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 228 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 228 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 228 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 228 263 (accept_3_2 13 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 228 263 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 228 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 228 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 263 (accept_3_2 10 228 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 228 263 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 228 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 228 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 228 263 (accept_3_2 7 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  228 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 228 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 228 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 228 263 (accept_3_2 4 228 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 228 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 228 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 228 263
  (Polychromatic418967fa.accept_22_2_8_21_1_16092 2 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 228 263 (accept_3_2 1 228 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  263)))))))))))))))))))))))))))))))))))) (allB_succ' 37 227 263 (Eq.refl Bool.true) (allA_succ_of_accept 36 227 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 227 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 227 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 227 263 (accept_3_2 34 227 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 227 263 (Polychromatic418967fa.accept_19_14_18_16_1_6530 33 227 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 227 263
  (Polychromatic418967fa.accept_17_15_6_8_1_6343 32 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 227 263 (accept_3_2 31 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 227 263 (Polychromatic418967fa.accept_20_10_7_3_1_16094 30 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 227 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 227 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 227 263 (accept_3_2 28 227 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 227 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 227 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 227 263
  (Polychromatic418967fa.accept_10_6_7_3_1_547 26 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 227 263 (accept_3_2 25 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 227 263 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 227 263 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 227 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 227 263 (accept_3_2 22 227 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 227 263 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 227
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 227 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 227 263 (accept_3_2 19 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 227 263 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 227 263 (Polychromatic418967fa.accept_19_17_18_16_1_10714 17 227 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 263 (accept_3_2 16 227 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 227 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 263
  (Polychromatic418967fa.accept_10_4_7_3_1_54 14 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 227 263 (accept_3_2 13 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 227 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 227 263 (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 227 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 263 (accept_3_2 10 227 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 263 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 227 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 227 263 (accept_3_2 7 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  227 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 227 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 227 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 263 (accept_3_2 4 227 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 263 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 227 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 263
  (Polychromatic418967fa.accept_19_2_18_16_1_5111 2 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 263 (accept_3_2 1 227 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  263))))))))))))))))))))))))))))))))))))) (allB_succ' 38 226 263 (Eq.refl Bool.true) (allA_of_3_0 38 226 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 225 263 (Eq.refl Bool.true) (allA_succ_of_accept 38 225 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 225 263 (accept_3_2 37 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 225 263 (Polychromatic418967fa.accept_24_12_9_23_1_7477 36 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 225 263 (Polychromatic418967fa.accept_17_1_4_8_1_5049 35 225 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 225 263 (accept_3_2 34 225 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 225 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 225 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 225 263 (accept_3_2 31 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 225 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 225 263 (Polychromatic418967fa.accept_17_12_4_8_1_5073 29 225 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 263 (accept_3_2 28 225 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 225
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 225 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 225 263 (accept_3_2 25 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 225 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 225 263 (Polychromatic418967fa.accept_22_1_5_21_1_16103 23 225 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 263 (accept_3_2 22 225 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 263 (Polychromatic418967fa.accept_20_1_5_3_1_7397 21 225
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 225 263 (accept_3_2 19 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 225 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 225 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 225 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 263 (accept_3_2 16 225 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 263 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 225 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 263 (accept_3_2 13 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 225 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 225 263 (Polychromatic418967fa.accept_27_11_9_20_1_16095 11 225 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 263 (accept_3_2 10 225 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 263 (Polychromatic418967fa.accept_21_9_15_11_1_7018 9 225
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 263 (accept_3_2 7 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  225 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 225 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 225 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 263 (accept_3_2 4 225 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 225 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 263 (accept_3_2 1 225 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  263))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 224 263 (Eq.refl Bool.true) (allA_succ_of_accept 39 224 263
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 224 263 (Polychromatic418967fa.accept_11_5_4_10_1_524 38 224 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 224 263 (accept_3_2 37 224 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 224 263 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 224 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 224 263
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 224 263 (accept_3_2 34 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 224 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 224 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 224 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 224 263 (accept_3_2 31 224 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 224 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 224 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 224 263
  (Polychromatic418967fa.accept_10_9_4_3_1_539 29 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 224 263 (accept_3_2 28 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 224 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 224 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 224 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 224 263 (accept_3_2 25 224 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 224 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 224 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 224 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 224 263 (accept_3_2 22 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 224 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 224 263 (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 224 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 224 263 (accept_3_2 19 224 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 224 263 (Polychromatic418967fa.accept_19_18_15_16_1_6528 18
  224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 224 263
  (Polychromatic418967fa.accept_10_7_4_3_1_560 17 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 224 263 (accept_3_2 16 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 224 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 224 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 224 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 224 263 (accept_3_2 13 224 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 224 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 224 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 224 263
  (Polychromatic418967fa.accept_19_11_15_16_1_9396 11 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 224 263 (accept_3_2 10 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 224 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 224 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 224 263 (Polychromatic418967fa.accept_19_8_15_16_1_5109 8 224
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 224 263 (accept_3_2 7 224 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 224 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 224 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 224 263 (accept_3_2 4 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  224 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 224 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 224 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 224 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 224 263 (accept_3_2 1 224 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 224 263)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 223 263 (Eq.refl
  Bool.true) (allA_of_3_0 41 223 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 222 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 222 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 222 263 (accept_3_2 40 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 222 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 222 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 222 263 (Polychromatic418967fa.accept_17_4_1_8_1_5070
  38 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 222 263 (accept_3_2 37
  222 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 222 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 222 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 222 263 (accept_3_2 34 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 222 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 222 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 222 263 (Polychromatic418967fa.accept_9_5_6_2_1_161
  32 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 222 263 (accept_3_2 31
  222 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 222 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 222 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 222 263 (accept_3_2 28 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 222 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 222 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 222 263 (Polychromatic418967fa.accept_9_8_6_2_1_744
  26 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 222 263 (accept_3_2 25
  222 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 222 263
  (Polychromatic418967fa.accept_13_11_1_3_1_910 24 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 222 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 222 263 (accept_3_2 22 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 222 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 222 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 222 263 (Polychromatic418967fa.accept_7_6_5_4_1_297
  20 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 222 263 (accept_3_2 19
  222 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 222 263
  (Polychromatic418967fa.accept_13_5_1_3_1_878 18 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 222 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 263 (accept_3_2 16 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 222 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 222 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 222 263 (Polychromatic418967fa.accept_9_5_6_2_1_161
  14 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 263 (accept_3_2 13
  222 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 222 263
  (Polychromatic418967fa.accept_9_3_6_2_1_160 12 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 222 263 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 222 263 (accept_3_2 10 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 222 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 222 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 8
  222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 263 (accept_3_2 7 222
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 222 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 263 (accept_3_2 4 222 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 222 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 222 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  222 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 263 (accept_3_2 1 222
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222 263)))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  43 221 263 (Eq.refl Bool.true) (allA_succ_of_accept 42 221 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 221 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 221 263
  (Polychromatic418967fa.accept_16_9_13_7_1_1509 41 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 221 263 (accept_3_2 40 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 221 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 221 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 221 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 221 263 (accept_3_2 37 221 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 221 263 (Polychromatic418967fa.accept_16_4_13_7_1_4522 36 221 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 221 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 221 263 (accept_3_2 34 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 221 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 221 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 32 221 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 221 263 (accept_3_2 31 221 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 221 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 221 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 221 263
  (Polychromatic418967fa.accept_28_1_25_11_1_10093 29 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 221 263 (accept_3_2 28 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 221 263 (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 221 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 221 263 (accept_3_2 25
  221 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 221 263
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 221 263 (Polychromatic418967fa.accept_19_4_12_16_1_2574 23 221 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 263 (accept_3_2 22 221 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 221 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 263
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 221 263 (accept_3_2 19 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 221 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 221 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 221 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 263 (accept_3_2 16 221 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 221 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 221 263 (accept_3_2 13 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 221 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 263 (Polychromatic418967fa.accept_22_11_1_21_1_6560 11 221 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 263 (accept_3_2 10 221 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 263 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 221 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 263 (accept_3_2 7 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 263 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 221 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 263 (accept_3_2 4 221 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 221 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 263 (accept_3_2 1 221 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  263))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 220 263 (Eq.refl Bool.true) (allA_of_3_0 44 220 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 219 263 (Eq.refl Bool.true) (allA_succ_of_accept 44 219 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 219 263 (accept_3_2 43 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 219 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 219 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 219 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 219 263 (accept_3_2 40 219 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 219 263 (Polychromatic418967fa.accept_19_1_10_16_1_6510 39 219 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 219 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 219 263 (accept_3_2 37 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 219 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 219 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 219 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 219 263 (accept_3_2 34 219 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 219 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 219 263 (accept_3_2 31 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 219 263 (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 219 263 (Polychromatic418967fa.accept_15_14_9_8_1_3165 29 219 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 263 (accept_3_2 28 219 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 219 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 219 263 (accept_3_2 25 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 219 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 219 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 219 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 263 (accept_3_2 22 219 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 219 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 263 (accept_3_2 19 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 219 263 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 219 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 219 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 263 (accept_3_2 16 219 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 219 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 263 (accept_3_2 13 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 219 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 263 (Polychromatic418967fa.accept_24_11_3_23_1_16089 11 219 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 263 (accept_3_2 10 219 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 219
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 263 (accept_3_2 7 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  219 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 219 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 219 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 263 (accept_3_2 4 219 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 263 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 219 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 263 (accept_3_2 1 219 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  263))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 218 263 (Eq.refl Bool.true) (allA_succ_of_accept 45
  218 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 218 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 218 263 (accept_3_2 43 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 218 263 (Polychromatic418967fa.accept_19_4_9_16_1_3811 42 218
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 218 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 218 263 (accept_3_2 40 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 218 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 218 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 218 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 218 263 (accept_3_2 37 218 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 218 263 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 218 263
  (Polychromatic418967fa.accept_10_5_8_3_1_229 35 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 218 263 (accept_3_2 34 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 218 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 218 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 218 263 (accept_3_2 31 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 218 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 218
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 218 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 218 263 (accept_3_2 28 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 218 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 218 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 218 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 218 263 (accept_3_2 25 218 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 218 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 218 263
  (Polychromatic418967fa.accept_11_1_9_10_1_184 23 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 218 263 (accept_3_2 22 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 218 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 218 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 218 263 (accept_3_2 19 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 218 263 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 218
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 218 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 218 263 (accept_3_2 16 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 218 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 218 263 (Polychromatic418967fa.accept_16_14_10_7_1_2363 14 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 218 263 (accept_3_2 13 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 218 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 218 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 218 263
  (Polychromatic418967fa.accept_10_1_8_3_1_947 11 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 218 263 (accept_3_2 10 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  218 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 218 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 218 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 218 263 (accept_3_2 7 218 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 218 263 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 218 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 218 263 (accept_3_2 4 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  218 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 218 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 218 263 (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 218 263 (accept_3_2 1 218 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 218 263)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 217 263
  (Eq.refl Bool.true) (allA_of_3_0 47 217 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 216 263 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 216 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 216 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 216 263 (accept_3_2 46 216 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 216 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 216 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 216 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 216 263 (accept_3_2 43 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 216 263 (Polychromatic418967fa.accept_19_4_7_16_1_6486 42 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 216 263 (Polychromatic418967fa.accept_16_9_8_7_1_4529 41 216 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 216 263 (accept_3_2 40 216 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 216 263 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 216
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 216 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 216 263 (accept_3_2 37 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 216 263 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 216 263 (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 216 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 216 263 (accept_3_2 34 216 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 216 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 216 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 216 263
  (Polychromatic418967fa.accept_15_2_6_8_1_754 32 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 216 263 (accept_3_2 31 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 216 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 216 263 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 216 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 216 263 (accept_3_2 28 216 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 216 263 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 216
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 216 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 216 263 (accept_3_2 25 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 216 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 216 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 216 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 263 (accept_3_2 22 216 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 216 263 (Polychromatic418967fa.accept_17_4_12_8_1_3833 21 216 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 216 263
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 216 263 (accept_3_2 19 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 216 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 216 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 216 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 216 263 (accept_3_2 16 216 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 216 263 (Polychromatic418967fa.accept_16_15_8_7_1_3407 15 216 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 263
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 216 263 (accept_3_2 13 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 216 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 216 263 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 216 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 216 263 (accept_3_2 10 216 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 216 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 216 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 216 263
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 216 263 (accept_3_2 7 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  216 263 (Polychromatic418967fa.accept_19_6_7_16_1_1418 6 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 216 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 216 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 263 (accept_3_2 4 216 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 216 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 216 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 216 263 (accept_3_2 1 216 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  263)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 215 263 (Eq.refl Bool.true) (allA_succ_of_accept 48
  215 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 215 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 47 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 215 263 (accept_3_2 46 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 215 263 (Polychromatic418967fa.accept_19_7_6_16_1_3818 45 215
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 215 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 215 263 (accept_3_2 43 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 215 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 215 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 215 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 215 263 (accept_3_2 40 215 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 215 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 215 263
  (Polychromatic418967fa.accept_10_8_5_3_1_543 38 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 215 263 (accept_3_2 37 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 215 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 215 263 (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 215 263 (accept_3_2 34 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 215 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 215 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 215 263 (accept_3_2 31 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 215 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 215 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 215 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 215 263 (accept_3_2 28 215 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 215 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 215 263
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 215 263 (accept_3_2 25 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 215 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 215 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 215 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 263 (accept_3_2 22 215 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 215 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 215 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 215 263 (accept_3_2 19 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 215 263 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 215 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 263 (accept_3_2 16 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 215 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 215 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 215 263 (accept_3_2 13 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 215 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 215 263 (Polychromatic418967fa.accept_13_11_7_3_1_894 11 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 263 (accept_3_2 10 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 215 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 215 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 215 263 (accept_3_2 7 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  215 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 215 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 215 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 263 (accept_3_2 4 215 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 215 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 263 (accept_3_2 1 215 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  263))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 214 263 (Eq.refl Bool.true) (allA_of_3_0 50 214
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 213 263 (Eq.refl Bool.true) (allA_succ_of_accept 50 213
  263 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 213 263 (accept_3_2 49 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 213 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 213 263 (Polychromatic418967fa.accept_13_8_5_3_1_427 47 213 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 213 263 (accept_3_2 46 213 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 213 263 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 213
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 213 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 213 263 (accept_3_2 43 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 213 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 213 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 213 263 (accept_3_2 40 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 213 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 213 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 213 263 (accept_3_2 37 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 213 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 213 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 263 (accept_3_2 34 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 213 263 (Polychromatic418967fa.accept_17_16_9_8_1_5063 33 213 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 213 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 213 263 (accept_3_2 31 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 213 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 213 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 263 (accept_3_2 28 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 213 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 213 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 213 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 213 263 (accept_3_2 25 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 213 263 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 213 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 263 (accept_3_2 22 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 213 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 263 (accept_3_2 19 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 213 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 213 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 263 (accept_3_2 16 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 213 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 263 (accept_3_2 13 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 213 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 213 263 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 213 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 263 (accept_3_2 10 213 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 263 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 213 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 263 (accept_3_2 7 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  213 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 213 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 263 (accept_3_2 4 213 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 213 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 263 (accept_3_2 1 213 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  263))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 212 263 (Eq.refl Bool.true) (allA_succ_of_accept
  51 212 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 212 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 212 263 (accept_3_2 49 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 212 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 212 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 212 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 212 263 (accept_3_2 46 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 212 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 212 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 212 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 212 263 (accept_3_2 43 212 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 212 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 212 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 212 263 (accept_3_2 40 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 212 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 212 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 212 263 (accept_3_2 37 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 212 263 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 212
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 212 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 212 263 (accept_3_2 34 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 212 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 212 263 (Polychromatic418967fa.accept_19_13_3_16_1_6467 32 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 212 263 (accept_3_2 31 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 212 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 212 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 212 263
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 212 263 (accept_3_2 28 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 212 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 212 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 212 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 212 263 (accept_3_2 25 212 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 212 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 212 263
  (Polychromatic418967fa.accept_14_9_2_11_1_780 23 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 212 263 (accept_3_2 22 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 212 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 212 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 212 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 212 263 (accept_3_2 19 212 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 212 263 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 212 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 212 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 212 263 (accept_3_2 16 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 212 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 212 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 212 263 (accept_3_2 13 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 212 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 212 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 212 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 212 263 (accept_3_2 10 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  212 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 212 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 212 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 263 (accept_3_2 7 212 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 212 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 212 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 212 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 212 263 (accept_3_2 4 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  212 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 212 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 212 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 263 (accept_3_2 1 212 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 263)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 211 263
  (Eq.refl Bool.true) (allA_of_3_0 53 211 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 210 263 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 210 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 210 263 (accept_3_2 52 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 210 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 210 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 210 263 (accept_3_2 49 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 210 263 (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 210 263 (Polychromatic418967fa.accept_20_7_10_3_1_949 47 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 210 263 (accept_3_2 46 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 210 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 210 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 210 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 210 263 (accept_3_2 43 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 210 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 210 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 210 263 (accept_3_2 40 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 210 263 (Polychromatic418967fa.accept_20_19_10_3_1_13274 39 210 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 210 263
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 38 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 210 263 (accept_3_2 37 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 210 263 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 210 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 210 263 (accept_3_2 34 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 210 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 210 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 210 263 (accept_3_2 31 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 210 263 (Polychromatic418967fa.accept_22_8_12_21_1_11444 30 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 210 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 210 263 (accept_3_2 28 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 210 263 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 210
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 210 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 210 263 (accept_3_2 25 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 210 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 210 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 210 263 (accept_3_2 22 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 210 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 210 263
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 210 263 (accept_3_2 19 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 210 263 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 210 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 263 (accept_3_2 16 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 210 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 210 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 210 263 (accept_3_2 13 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 210 263 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 210 263 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 263 (accept_3_2 10 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 210 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 210 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 210 263 (accept_3_2 7 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  210 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 210 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 263 (accept_3_2 4 210 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 263 (Polychromatic418967fa.accept_19_3_1_16_1_7947 3 210 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 263
  (Polychromatic418967fa.accept_11_2_1_10_1_196 2 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 210 263 (accept_3_2 1 210 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 209 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 209 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 209 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 209 263 (Polychromatic418967fa.accept_24_5_17_23_1_14285 53
  209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 209 263 (accept_3_2 52
  209 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 209 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 209 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 209 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 209 263 (accept_3_2 49 209 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 209 263 (Polychromatic418967fa.accept_21_6_20_11_1_7067 48 209 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 209 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 209 263 (accept_3_2 46 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 209 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 209 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 263 (accept_3_2 43 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 209 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 263
  (Polychromatic418967fa.accept_13_2_1_3_1_419 41 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 209 263 (accept_3_2 40 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 209 263 (Polychromatic418967fa.accept_15_9_14_8_1_1396 39 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 209 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 263 (accept_3_2 37 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 263 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 209 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 263
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 209 263 (accept_3_2 34 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 209 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 209 263 (Polychromatic418967fa.accept_13_6_1_3_1_1522 32 209 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 263 (accept_3_2 31 209 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 209 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 263
  (Polychromatic418967fa.accept_17_12_5_8_1_7680 29 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 209 263 (accept_3_2 28 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 209 263 (Polychromatic418967fa.accept_21_6_20_11_1_7067 27 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 209 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 263 (accept_3_2 25 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 209 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 263 (accept_3_2 22 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 263 (Polychromatic418967fa.accept_15_6_14_8_1_245 21 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 263 (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 209 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 263 (accept_3_2 19 209 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 209 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 263 (accept_3_2 16 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 263 (Polychromatic418967fa.accept_13_2_1_3_1_419 15 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 263 (accept_3_2 13 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 209 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 263
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 263 (accept_3_2 10 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 263 (Polychromatic418967fa.accept_16_8_1_7_1_2355 8 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 263 (accept_3_2 7 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 209 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 263 (accept_3_2 4 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 209 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 263 (accept_3_2 1 209 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 263))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 208 263
  (Eq.refl Bool.true) (allA_of_3_0 56 208 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 207 263 (Eq.refl
  Bool.true) (allA_succ_of_accept 56 207 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 263 (accept_3_2 55 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 207 263 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 207 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 207 263
  (Polychromatic418967fa.accept_24_5_15_23_1_5647 53 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 207 263 (accept_3_2 52 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 207 263 (Polychromatic418967fa.accept_16_3_15_7_1_3417 51 207 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 207 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 207 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 263 (accept_3_2 49 207 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 263 (Polychromatic418967fa.accept_13_9_12_3_1_907
  48 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 207 263
  (Polychromatic418967fa.accept_17_13_3_8_1_6310 47 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 263 (accept_3_2 46 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 207 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 207 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 263 (accept_3_2 43 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 263 (Polychromatic418967fa.accept_24_18_15_23_1_9254 42 207 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 263
  (Polychromatic418967fa.accept_11_8_9_10_1_503 41 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 207 263 (accept_3_2 40 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 207 263 (Polychromatic418967fa.accept_17_5_3_8_1_1697 39 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 207 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 263 (accept_3_2 37 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 263 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 207 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 263 (accept_3_2 34 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 207 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 207 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 263 (accept_3_2 31 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 207 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 263
  (Polychromatic418967fa.accept_17_12_3_8_1_7627 29 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 207 263 (accept_3_2 28 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 207 263 (Polychromatic418967fa.accept_16_11_15_7_1_5654 27 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 207 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 263 (accept_3_2 25 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 263 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 207 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 263
  (Polychromatic418967fa.accept_11_1_9_10_1_184 23 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 263 (accept_3_2 22 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 207 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 207 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 263 (accept_3_2 19 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 263 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 207 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 263
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 263 (accept_3_2 16 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 207 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 207 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 263 (accept_3_2 13 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 207 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 263
  (Polychromatic418967fa.accept_15_11_12_8_1_739 11 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 263 (accept_3_2 10 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  207 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 207 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 263 (accept_3_2 7 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 263 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 207 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 263 (accept_3_2 4 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 263 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 207 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 263 (accept_3_2 1 207 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 207 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 206 263
  (Eq.refl Bool.true) (allA_succ_of_accept 57 206 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 206 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 206 263 (accept_3_2 55 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 206 263 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 206 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 206 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 206 263 (accept_3_2 52 206 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 206 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 206 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 206 263 (accept_3_2 49 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 206 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 206 263 (Polychromatic418967fa.accept_10_7_6_3_1_927 47 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 206 263 (accept_3_2 46 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 206 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 206 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 206 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 206 263 (accept_3_2 43 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 206 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 206 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 206 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 206 263 (accept_3_2 40 206 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 206 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 206 263
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 206 263 (accept_3_2 37 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 206 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 206 263 (Polychromatic418967fa.accept_14_7_10_11_1_8112 35 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 206 263 (accept_3_2 34 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 206 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 206 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 206 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 206 263 (accept_3_2 31 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 206 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 206 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 206 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 206 263 (accept_3_2 28 206 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 206 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 206 263
  (Polychromatic418967fa.accept_16_10_14_7_1_2372 26 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 206 263 (accept_3_2 25 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 206 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 206 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 206 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 206 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 206 263 (accept_3_2 22 206 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 206 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 206 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 206 263 (accept_3_2 19 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 206 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 206 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 206 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 206 263 (accept_3_2 16 206 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 206 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 206 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 206 263 (accept_3_2 13 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 206 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 206 263 (Polychromatic418967fa.accept_17_11_2_8_1_7569 11 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 263 (accept_3_2 10 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 206 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 206 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 206 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 206 263 (accept_3_2 7 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  206 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 206 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 206 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 263 (accept_3_2 4 206 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 206 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 263
  (Polychromatic418967fa.accept_13_2_11_3_1_873 2 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 263 (accept_3_2 1 206 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 205 263 (Eq.refl Bool.true) (allA_of_3_0
  59 205 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 204 263 (Eq.refl Bool.true) (allA_succ_of_accept 59
  204 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 204 263 (accept_3_2 58 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 204 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 204 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 204 263 (Polychromatic418967fa.accept_16_8_12_7_1_2399 56 204
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 204 263 (accept_3_2 55 204
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 204 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 204 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 204 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 204 263 (accept_3_2 52 204 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 204 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 204 263 (Polychromatic418967fa.accept_9_5_6_2_1_161
  50 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 204 263 (accept_3_2 49
  204 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 204 263
  (Polychromatic418967fa.accept_9_3_6_2_1_160 48 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 204 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 204 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 204 263 (accept_3_2 46 204 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 204 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 204 263 (Polychromatic418967fa.accept_9_8_6_2_1_744
  44 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 204 263 (accept_3_2 43
  204 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 204 263
  (Polychromatic418967fa.accept_23_19_20_10_1_14360 42 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 204 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 204 263 (accept_3_2 40 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 204 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 204 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 204 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 204 263 (accept_3_2 37 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 204 263 (Polychromatic418967fa.accept_16_4_12_7_1_4475 36 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 204 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 204 263 (accept_3_2 34 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 204 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 204 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 204 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 204 263 (accept_3_2 31 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 204 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 204 263 (Polychromatic418967fa.accept_10_9_4_3_1_539 29 204 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 204 263 (accept_3_2 28 204 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 204 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 204 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 204 263 (accept_3_2 25 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 204 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 204 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 204 263 (accept_3_2 22 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 204 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 204 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 263
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 204 263 (accept_3_2 19 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 204 263 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 204 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 204 263 (accept_3_2 16 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 204 263 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 204 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 204 263 (accept_3_2 13 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 204 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 204 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 263 (accept_3_2 10 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 204 263 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 204 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 204 263 (accept_3_2 7 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  204 263 (Polychromatic418967fa.accept_13_6_9_3_1_915 6 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 204 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 204 263 (accept_3_2 4 204 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 204 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 204 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 263
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 2 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 204 263 (accept_3_2 1 204 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 203 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 203 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 203 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 203 263 (Polychromatic418967fa.accept_11_4_5_10_1_926 59 203
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 203 263 (accept_3_2 58 203
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 203 263
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 203 263 (Polychromatic418967fa.accept_19_18_13_16_1_9366 56 203 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 203 263 (accept_3_2 55 203 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 203 263 (Polychromatic418967fa.accept_21_12_14_11_1_3921 54 203 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 203 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 203 263 (accept_3_2 52 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 203 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 203 263 (Polychromatic418967fa.accept_11_6_5_10_1_2724 50 203 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 203 263 (accept_3_2 49 203 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 203 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 203 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 203 263
  (Polychromatic418967fa.accept_16_15_11_7_1_6951 47 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 203 263 (accept_3_2 46 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 203 263 (Polychromatic418967fa.accept_14_3_7_11_1_765 45 203 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 203 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 203 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 203 263 (accept_3_2 43 203 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 203 263 (Polychromatic418967fa.accept_9_6_5_2_1_421
  42 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 203 263
  (Polychromatic418967fa.accept_17_7_16_8_1_7613 41 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 203 263 (accept_3_2 40 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 203 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 203 263 (Polychromatic418967fa.accept_14_10_7_11_1_3015 38 203 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 263 (accept_3_2 37 203 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 203 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 203 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 203 263 (accept_3_2 34 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 203 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 203 263 (Polychromatic418967fa.accept_14_4_7_11_1_790 32 203 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 263 (accept_3_2 31 203 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 203 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 263
  (Polychromatic418967fa.accept_19_10_13_16_1_10734 29 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 203 263 (accept_3_2 28 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 203 263 (Polychromatic418967fa.accept_21_6_14_11_1_10103 27 203 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 263 (Polychromatic418967fa.accept_9_8_5_2_1_422
  26 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 263 (accept_3_2 25
  203 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 263
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 203 263 (Polychromatic418967fa.accept_21_2_14_11_1_7060 23 203 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 263 (accept_3_2 22 203 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 203 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 263
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 203 263 (accept_3_2 19 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 203 263 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 203 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 203 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 263 (accept_3_2 16 203 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 203 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 203 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 263
  (Polychromatic418967fa.accept_17_14_16_8_1_3861 14 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 203 263 (accept_3_2 13 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 203 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 203 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 263 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 203
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 263 (accept_3_2 10 203
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 263
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 203 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 203 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 263 (accept_3_2 7 203 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 203 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 203 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 263 (Polychromatic418967fa.accept_13_5_8_3_1_1535
  5 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 263 (accept_3_2 4
  203 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 263
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 203 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 203 263 (Polychromatic418967fa.accept_16_2_11_7_1_2352 2 203 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 263 (accept_3_2 1 203 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 203 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 202 263
  (Eq.refl Bool.true) (allA_of_3_0 62 202 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 201 263 (Eq.refl
  Bool.true) (allA_succ_of_accept 62 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 201 263 (accept_3_2 61 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 201 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 201 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 201 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 201 263 (accept_3_2 58 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 201 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 201 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 263 (accept_3_2 55 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 201 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 201 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 201 263 (accept_3_2 52 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 201 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 263 (accept_3_2 49 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 201 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 201 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 201 263
  (Polychromatic418967fa.accept_15_2_6_8_1_754 47 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 201 263 (accept_3_2 46 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 201 263 (Polychromatic418967fa.accept_16_13_9_7_1_4532 45 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 201 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 263 (accept_3_2 43 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 201 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 201 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 201 263 (accept_3_2 40 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 201 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 263 (accept_3_2 37 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 201 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 201 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 201 263 (accept_3_2 34 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 201 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 201 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 263 (accept_3_2 31 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 201 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 201 263 (accept_3_2 28 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 201 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 263 (accept_3_2 25 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 201 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 201 263 (accept_3_2 22 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 201 263 (Polychromatic418967fa.accept_19_2_11_16_1_6525 21 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 201 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 263 (accept_3_2 19 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 201 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 201 263 (accept_3_2 16 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 201 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 263 (accept_3_2 13 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 201 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 263
  (Polychromatic418967fa.accept_17_11_14_8_1_2729 11 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 201 263 (accept_3_2 10 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 201 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 201 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 263 (accept_3_2 7 201 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 263 (accept_3_2 4 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 201 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 263 (accept_3_2 1 201 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  200 263 (Eq.refl Bool.true) (allA_succ_of_accept 63 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 200 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 200 263 (accept_3_2 61 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 200 263 (Polychromatic418967fa.accept_13_8_5_3_1_427 60 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 200 263 (Polychromatic418967fa.accept_15_14_5_8_1_3175 59 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 200 263 (accept_3_2 58 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 200 263
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 200 263 (accept_3_2 55 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 200 263 (Polychromatic418967fa.accept_13_2_5_3_1_406 54 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 200 263 (Polychromatic418967fa.accept_13_1_5_3_1_888 53 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 200 263 (accept_3_2 52 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 200 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 200 263 (accept_3_2 49 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 200 263 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 200 263 (Polychromatic418967fa.accept_13_8_5_3_1_427 47 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 200 263 (accept_3_2 46 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 200 263
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 200 263 (accept_3_2 43 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 200 263 (Polychromatic418967fa.accept_15_12_5_8_1_5247 42 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 200 263 (Polychromatic418967fa.accept_13_2_5_3_1_406 41 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 200 263 (accept_3_2 40 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 200 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 200 263 (accept_3_2 37 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 200 263 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 200 263 (Polychromatic418967fa.accept_13_9_5_3_1_428 35 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 200 263 (accept_3_2 34 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 200 263
  (Polychromatic418967fa.accept_13_6_5_3_1_426 32 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 200 263 (accept_3_2 31 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 200 263 (Polychromatic418967fa.accept_22_8_2_21_1_9874 30 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 200 263 (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 200 263 (accept_3_2 28 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 200 263 (accept_3_2 25 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 200 263 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 200 263 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 263 (accept_3_2 22 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 200 263
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 20 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 200 263 (accept_3_2 19 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 200 263 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 200 263 (Polychromatic418967fa.accept_16_1_8_7_1_3377 17 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 200 263 (accept_3_2 16 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 200 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 200 263 (accept_3_2 13 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 200 263 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 200 263 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 200 263 (accept_3_2 10 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 263
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 200 263 (accept_3_2 7 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  200 263 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 200 263 (Polychromatic418967fa.accept_17_5_13_8_1_7556 5 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 263 (accept_3_2 4 200 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 263 (accept_3_2 1 200 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 199 263 (Eq.refl Bool.true)
  (allA_of_3_0 65 199 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 198 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 198 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 198 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 198 263 (accept_3_2 64 198 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 198 263 (Polychromatic418967fa.accept_16_15_6_7_1_4512 63 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 198 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 198 263 (accept_3_2 61 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 198 263 (Polychromatic418967fa.accept_17_9_11_8_1_5077 60 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 198 263 (Polychromatic418967fa.accept_23_13_14_10_1_14470 59 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 198 263 (accept_3_2 58 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 198 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 198 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 198 263
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 198 263 (accept_3_2 55 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 198 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 198 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 198 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 198 263 (accept_3_2 52 198 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 198 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 198 263
  (Polychromatic418967fa.accept_15_5_3_8_1_748 50 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 198 263 (accept_3_2 49 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 198 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 198 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 198 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 198 263 (accept_3_2 46 198 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 198 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 198 263
  (Polychromatic418967fa.accept_19_6_8_16_1_13419 44 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 198 263 (accept_3_2 43 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 198 263 (Polychromatic418967fa.accept_15_12_3_8_1_5245 42 198 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 198 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 198 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 198 263 (accept_3_2 40 198 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 198 263 (Polychromatic418967fa.accept_15_9_3_8_1_3155
  39 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 198 263
  (Polychromatic418967fa.accept_26_12_16_3_1_16102 38 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 198 263 (accept_3_2 37 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 198 263 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 198 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 198 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 198
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 198 263 (accept_3_2 34 198
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 198 263 (Polychromatic418967fa.accept_4_1_2_3_1_9
  33 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 198 263
  (Polychromatic418967fa.accept_25_7_23_13_1_16101 32 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 198 263 (accept_3_2 31 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 198 263 (Polychromatic418967fa.accept_19_11_8_16_1_7988 30 198 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 198 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 198 263 (accept_3_2 28
  198 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 198 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 198 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 198 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 263 (accept_3_2 25 198 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 198 263 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 198 263
  (Polychromatic418967fa.accept_14_9_2_11_1_780 23 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 198 263 (accept_3_2 22 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 198 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 198 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 198 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 263 (accept_3_2 19 198 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 263 (Polychromatic418967fa.accept_17_1_11_8_1_2725 18 198 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 198 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 198 263 (accept_3_2 16 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 198 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 198 263 (Polychromatic418967fa.accept_17_14_11_8_1_3854 14 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 263 (accept_3_2 13 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 198 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 198 263
  (Polychromatic418967fa.accept_10_1_8_3_1_947 11 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 198 263 (accept_3_2 10 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  198 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 198 263 (Polychromatic418967fa.accept_20_8_18_3_1_10560 8 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 263 (accept_3_2 7 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 198 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 198 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 198 263 (accept_3_2 4 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  198 263 (Polychromatic418967fa.accept_27_3_9_20_1_16100 3 198 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 198 263 (Polychromatic418967fa.accept_17_2_11_8_1_2726 2 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 263 (accept_3_2 1 198 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 198 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 67 197 263 (Eq.refl Bool.true) (allA_succ_of_accept 66 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27
  66 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 197 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 65 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 197 263 (accept_3_2 64 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 197 263 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 197 263 (accept_3_2 61 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 197 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 197 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 197 263 (accept_3_2 58 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 197 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 197 263 (Polychromatic418967fa.accept_10_6_7_3_1_547 56 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 197 263 (accept_3_2 55 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 197 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 197 263
  (Polychromatic418967fa.accept_13_1_2_3_1_911 53 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 197 263 (accept_3_2 52 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 197 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 197 263 (accept_3_2 49 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 197 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 197 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 197 263 (accept_3_2 46 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 197 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 197 263 (Polychromatic418967fa.accept_10_4_7_3_1_54 44 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 197 263 (accept_3_2 43 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 197 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 197 263 (accept_3_2 40 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 197 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 197 263 (accept_3_2 37 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 197 263 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 197 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 197 263 (accept_3_2 34 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 197 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 197 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 197 263 (accept_3_2 31 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 197 263
  (Polychromatic418967fa.accept_17_12_10_8_1_5039 29 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 197 263 (accept_3_2 28 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 197 263 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 197 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 197 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 263 (accept_3_2 25 197 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 197 263 (Polychromatic418967fa.accept_7_3_1_4_1_121
  24 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 197 263 (accept_3_2 22 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 197 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 197 263 (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 263 (accept_3_2 19 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 197 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 197 263 (accept_3_2 16 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 197 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 263 (accept_3_2 13 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 263
  (Polychromatic418967fa.accept_13_11_2_3_1_883 11 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 263 (accept_3_2 10 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 263 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 263 (Polychromatic418967fa.accept_19_8_7_16_1_5117 8 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 263 (accept_3_2 7 197 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 197 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 263 (accept_3_2 4 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 197 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 263 (accept_3_2 1 197 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 196 263 (Eq.refl Bool.true) (allA_of_3_0 68 196 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 195 263
  (Eq.refl Bool.true) (allA_succ_of_accept 68 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 195 263 (accept_3_2 67 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 195 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 195 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 195 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 195 263 (accept_3_2 64 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 195 263 (Polychromatic418967fa.accept_16_15_3_7_1_3389 63 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 195 263 (accept_3_2 61 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 195 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 195 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 195 263 (accept_3_2 58 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 195 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 263 (accept_3_2 55 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 195 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 195 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 195 263 (accept_3_2 52 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 195 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 195 263 (accept_3_2 49 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 195 263 (accept_3_2 46 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 195 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 263 (accept_3_2 43 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 195 263 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 195 263 (accept_3_2 40 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 195 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 263 (accept_3_2 37 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 195 263 (accept_3_2 34 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 195 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 263 (accept_3_2 31 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 263
  (Polychromatic418967fa.accept_19_10_5_16_1_6522 29 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 195 263 (accept_3_2 28 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 195 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 195 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 195 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 263 (accept_3_2 25 195 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 263 (accept_3_2 22 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 195 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 263 (accept_3_2 19 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 263 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 263 (accept_3_2 16 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 195 263 (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 263 (accept_3_2 13 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 263
  (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 263 (accept_3_2 10 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 263 (accept_3_2 7 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 263 (Polychromatic418967fa.accept_18_6_15_11_1_3141 6 195 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 263 (accept_3_2 4 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 195 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 263 (accept_3_2 1 195 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 195 263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 194 263 (Eq.refl Bool.true) (allA_succ_of_accept 69 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9
  69 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 194 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 194 263 (accept_3_2 67 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 194 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 194 263 (accept_3_2 64 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 194 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 194 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 194 263 (accept_3_2 61 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 194 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 194 263 (Polychromatic418967fa.accept_10_9_4_3_1_539 59 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 194 263 (accept_3_2 58 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 194 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 194 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 194 263 (accept_3_2 55 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 194 263 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 194 263 (accept_3_2 52 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 194 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 194 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 194 263 (accept_3_2 49 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 194 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 194 263 (Polychromatic418967fa.accept_10_7_4_3_1_560 47 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 194 263 (accept_3_2 46 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 194 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 194 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 194 263 (accept_3_2 43 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 194 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 194 263 (accept_3_2 40 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 194 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 194 263
  (Polychromatic418967fa.accept_17_4_7_8_1_7491 38 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 194 263 (accept_3_2 37 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 194 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 194 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 194 263 (accept_3_2 34 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 194 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 194 263 (accept_3_2 31 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 194 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 263 (accept_3_2 28 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 194 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 194 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 194 263 (accept_3_2 25 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 194 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 194 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 194 263 (accept_3_2 22 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 194 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 194 263 (accept_3_2 19 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 194 263 (Polychromatic418967fa.accept_17_1_7_8_1_6347 18 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 194 263 (accept_3_2 16 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 194 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 194 263
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 194 263 (accept_3_2 13 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 194 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 194 263 (Polychromatic418967fa.accept_16_11_2_7_1_3374 11 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 263 (accept_3_2 10 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 194 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 263 (accept_3_2 7 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 263 (accept_3_2 4 194 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 194 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 263 (accept_3_2 1 194 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 193 263 (Eq.refl Bool.true)
  (allA_of_3_0 71 193 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 192 263 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 192 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 192 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 192 263 (accept_3_2 70 192 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 192 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 192 263 (Polychromatic418967fa.accept_9_5_3_2_1_171
  68 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 192 263 (accept_3_2 67
  192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 192 263
  (Polychromatic418967fa.accept_27_12_3_20_1_16099 66 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 192 263 (Polychromatic418967fa.accept_10_5_2_3_1_239 65 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 192 263 (accept_3_2 64 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 192 263 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 192
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 192 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 192 263 (accept_3_2 61 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 192 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 192 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 192 263 (accept_3_2 58 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 192 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 192 263
  (Polychromatic418967fa.accept_15_11_12_8_1_739 56 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 192 263 (accept_3_2 55 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 192 263 (Polychromatic418967fa.accept_13_2_10_3_1_1538 54 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 192 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 192 263 (accept_3_2 52 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 192 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 192 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 192 263 (accept_3_2 49 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 192 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 192 263 (Polychromatic418967fa.accept_17_13_5_8_1_896 47 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 192 263 (accept_3_2 46 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 192 263 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 192
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 192 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 192 263 (accept_3_2 43 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 192 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 192 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 263 (accept_3_2 40 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 192 263 (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 192 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 192 263
  (Polychromatic418967fa.accept_23_15_8_10_1_12896 38 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 192 263 (accept_3_2 37 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 192 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 192 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 192 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 192 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 263 (accept_3_2 34 192 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 192 263 (Polychromatic418967fa.accept_9_6_3_2_1_431
  33 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 192 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 192 263 (accept_3_2 31 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 192 263 (Polychromatic418967fa.accept_17_13_5_8_1_896 30 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 192 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 263 (accept_3_2 28 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 192 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 192 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 192 263 (accept_3_2 25 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 192 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 192 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 263 (accept_3_2 22 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 192 263 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 192 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 192 263 (accept_3_2 19 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 192 263 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 192 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 263 (accept_3_2 16 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 192 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 192 263 (accept_3_2 13 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 192 263 (Polychromatic418967fa.accept_17_12_5_8_1_7680 12 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 192 263 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 263 (accept_3_2 10 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 263 (Polychromatic418967fa.accept_18_9_12_11_1_5642 9 192
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 192 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 192 263 (accept_3_2 7 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  192 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 192 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 263 (accept_3_2 4 192 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 263 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 192 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 263
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 192 263 (accept_3_2 1 192 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_263_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


