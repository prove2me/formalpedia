-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch269
-- name    : Polychromatic418967fa_Branch269
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:31:42.599007+00:00
-- url     : https://prove2.me/theorems/e9573c2f-7f1c-41e1-9d2a-b58a7b0b3ba0
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch269_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_269 : allB 269 269 :=
  allB_succ' 2 268 269 (Eq.refl Bool.true) (allA_of_3_0 2 268 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  267 269 (Eq.refl Bool.true) (allA_succ_of_accept 2 267 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 267 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 269 (accept_3_2 1 267 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 267 269))) (allB_succ' 4 266 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 266 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 266 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 266 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 266 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 266 269 (accept_3_2 1 266 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 266 269)))) (allB_succ' 5 265 269 (Eq.refl Bool.true) (allA_of_3_0
  5 265 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 264 269 (Eq.refl Bool.true) (allA_succ_of_accept 5
  264 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 264 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 264 269 (accept_3_2 4 264 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 264 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 264 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 264 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 264 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 264 269 (accept_3_2 1 264 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 264 269)))))) (allB_succ' 7 263 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 263 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 263 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 263 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 263 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 263 269 (accept_3_2 4 263 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 263 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  263 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 263 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 263 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 263 269 (accept_3_2 1 263 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 263 269)))))))
  (allB_succ' 8 262 269 (Eq.refl Bool.true) (allA_of_3_0 8 262 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 261 269 (Eq.refl Bool.true) (allA_succ_of_accept 8 261 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 261 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 261 269 (accept_3_2 7 261 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 261 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  261 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 261 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 261 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 261 269 (accept_3_2 4 261 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  261 269 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 261 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 261 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 261 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 261 269 (accept_3_2 1 261 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 261 269))))))))) (allB_succ' 10 260 269 (Eq.refl Bool.true) (allA_succ_of_accept 9 260
  269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 260 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 260 269 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 260 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 260 269 (accept_3_2 7 260 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 260 269 (Polychromatic418967fa.accept_15_6_5_14_1_429 6 260 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 260 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  260 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 260 269 (accept_3_2 4 260
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 260 269 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 260 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 260 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 260 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 260 269 (accept_3_2 1 260 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 260
  269)))))))))) (allB_succ' 11 259 269 (Eq.refl Bool.true) (allA_of_3_0 11 259 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 258 269 (Eq.refl Bool.true) (allA_succ_of_accept 11 258 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 258 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 258 269 (accept_3_2 10 258 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  258 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 258 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 258 269 (Polychromatic418967fa.accept_13_8_11_9_1_593 8 258 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 258 269 (accept_3_2 7 258 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 258 269 (Polychromatic418967fa.accept_17_6_3_14_1_2078 6 258 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 258 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 258 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 258 269 (accept_3_2 4 258 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  258 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 258 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 258 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 258 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 258 269 (accept_3_2 1 258 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 258 269)))))))))))) (allB_succ' 13 257 269 (Eq.refl Bool.true) (allA_succ_of_accept 12
  257 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 257 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 257 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 257 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 257 269 (accept_3_2 10 257 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 257 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 257 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 257 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 257 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 257 269 (accept_3_2 7 257 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  257 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 257 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 257 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 257 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 257 269 (accept_3_2 4 257 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 257 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 257 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 257 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 257 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 257 269 (accept_3_2 1 257 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 257
  269))))))))))))) (allB_succ' 14 256 269 (Eq.refl Bool.true) (allA_of_3_0 14 256 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 255 269 (Eq.refl Bool.true) (allA_succ_of_accept 14 255 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 255 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 255 269 (accept_3_2 13 255 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 255 269 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 255 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 255 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 255 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 255 269 (accept_3_2 10 255 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 255 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 255 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 255 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 255 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 255 269 (accept_3_2 7 255 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  255 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 255 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 255 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 255 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 255 269 (accept_3_2 4 255 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 269 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3 255 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 255 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 255 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 255 269 (accept_3_2 1 255 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 255
  269))))))))))))))) (allB_succ' 16 254 269 (Eq.refl Bool.true) (allA_succ_of_accept 15 254 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 254 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 254 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 254 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 254 269 (accept_3_2 13 254 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 254 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 254 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 254 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  254 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 254 269 (accept_3_2 10
  254 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 254 269
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 254 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 254 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 254 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 254 269 (accept_3_2 7 254 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 254 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 254 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 254 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5
  254 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 254 269 (accept_3_2 4 254
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 254 269 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 254 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 254 269
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 2 254 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 254 269 (accept_3_2 1 254 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 254
  269)))))))))))))))) (allB_succ' 17 253 269 (Eq.refl Bool.true) (allA_of_3_0 17 253 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 252 269 (Eq.refl Bool.true) (allA_succ_of_accept 17 252 269
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 252 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 252 269 (accept_3_2 16 252 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 252 269 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 252 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 252 269 (Polychromatic418967fa.accept_13_1_5_9_1_226 14 252 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 252 269 (accept_3_2 13 252 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 252 269 (Polychromatic418967fa.accept_26_12_18_9_1_16466 12
  252 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 252 269
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 252 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 252 269 (accept_3_2 10 252 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  252 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 252 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 252 269 (Polychromatic418967fa.accept_16_8_12_13_1_3851 8 252 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 252 269 (accept_3_2 7 252 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 252 269 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 252 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 252 269
  (Polychromatic418967fa.accept_27_5_9_26_1_16465 5 252 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 252 269 (accept_3_2 4 252 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  252 269 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 252 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 252 269 (Polychromatic418967fa.accept_13_2_5_9_1_610 2 252 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 252 269 (accept_3_2 1 252 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 252 269)))))))))))))))))) (allB_succ' 19 251 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 251 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 251 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 251 269 (Polychromatic418967fa.accept_24_17_11_5_1_7987 17 251
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 251 269 (accept_3_2 16 251
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 251 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 251 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 251 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 251 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 251 269 (accept_3_2 13 251 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 251 269 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 251 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 251 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 251 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 251 269 (accept_3_2 10 251 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  251 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 251 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 251 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 251 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 251 269 (accept_3_2 7 251 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 251 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 251 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 251 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 251 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 251 269 (accept_3_2 4 251 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  251 269 (Polychromatic418967fa.accept_15_3_11_14_1_1705 3 251 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 251 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 251 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 251 269 (accept_3_2 1 251 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 251 269))))))))))))))))))) (allB_succ' 20 250 269 (Eq.refl Bool.true) (allA_of_3_0 20
  250 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 249 269 (Eq.refl Bool.true) (allA_succ_of_accept 20
  249 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 249 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 249 269 (accept_3_2 19 249 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 249 269 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 249 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 249 269 (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 249
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 249 269 (accept_3_2 16 249
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 249 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 249 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 249 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 249 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 269 (accept_3_2 13 249 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 249 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 249 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 249 269 (Polychromatic418967fa.accept_9_2_6_8_1_321
  11 249 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 249 269 (accept_3_2 10
  249 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 249 269
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 249 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 249 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 249 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 269 (accept_3_2 7 249 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 249 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 249 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 5
  249 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 269 (accept_3_2 4 249
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 249 269
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 249 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 249 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 249 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 269 (accept_3_2 1 249 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 249 269))))))))))))))))))))) (allB_succ' 22 248 269 (Eq.refl Bool.true) (allA_succ_of_accept 21
  248 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 248 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 248 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 248 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 248 269 (accept_3_2 19 248 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 248 269 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 248 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 248 269
  (Polychromatic418967fa.accept_10_7_8_9_1_785 17 248 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 248 269 (accept_3_2 16 248 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 248 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 248 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 248 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 248 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 248 269 (accept_3_2 13 248 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 248 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 248 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 248 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 248 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 248 269 (accept_3_2 10 248 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  248 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 248 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 248 269 (Polychromatic418967fa.accept_13_8_1_9_1_1178 8 248 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 248 269 (accept_3_2 7 248 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 248 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 248 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 248 269
  (Polychromatic418967fa.accept_13_5_1_9_1_618 5 248 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 248 269 (accept_3_2 4 248 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  248 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 248 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 248 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 248 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 248 269 (accept_3_2 1 248 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 248 269)))))))))))))))))))))) (allB_succ' 23 247 269 (Eq.refl Bool.true) (allA_of_3_0
  23 247 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 246 269 (Eq.refl Bool.true) (allA_succ_of_accept 23
  246 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 246 269 (accept_3_2 22 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 246 269 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 246 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 246 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 246 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 246 269 (accept_3_2 19 246 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 246 269 (Polychromatic418967fa.accept_7_4_1_3_1_277
  18 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 246 269
  (Polychromatic418967fa.accept_20_17_6_9_1_6434 17 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 246 269 (accept_3_2 16 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 246 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 246 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 246 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 246 269 (accept_3_2 13 246 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 246 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 246 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 246 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 246 269 (accept_3_2 10 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  246 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 246 269 (Polychromatic418967fa.accept_13_8_12_9_1_1168 8 246 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 246 269 (accept_3_2 7 246 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 246 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 246 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 246 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 246 269 (accept_3_2 4 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  246 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 246 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 246 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 246 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 269 (accept_3_2 1 246 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 246 269)))))))))))))))))))))))) (allB_succ' 25 245 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 24 245 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 245 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 245 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 245 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 245 269 (accept_3_2 22 245 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 245 269 (Polychromatic418967fa.accept_9_3_2_8_1_108
  21 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 245 269
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 20 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 245 269 (accept_3_2 19 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 245 269 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 245 269 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 245 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 245 269 (accept_3_2 16 245 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 245 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 245 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 245 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 245 269 (accept_3_2 13 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 245 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 245 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 245 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 245 269 (accept_3_2 10 245 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 245 269 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 245 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 245 269
  (Polychromatic418967fa.accept_11_8_3_5_1_355 8 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 245 269 (accept_3_2 7 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  245 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 245 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 245 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 245 269 (accept_3_2 4 245 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 245 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 269
  (Polychromatic418967fa.accept_13_2_11_9_1_591 2 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 269 (accept_3_2 1 245 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245
  269))))))))))))))))))))))))) (allB_succ' 26 244 269 (Eq.refl Bool.true) (allA_of_3_0 26 244 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 243 269 (Eq.refl Bool.true) (allA_succ_of_accept 26 243 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 243 269 (accept_3_2 25 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 243 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 243 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 243 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 269 (accept_3_2 22 243 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 243 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 243 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 243 269 (accept_3_2 19 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 243 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 243 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 243 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 269 (accept_3_2 16 243 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 243 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 243 269 (accept_3_2 13 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 243 269 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 243 269 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 243 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 269 (accept_3_2 10 243 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 243 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 243 269 (accept_3_2 7 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  243 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 243 269 (Polychromatic418967fa.accept_21_5_12_17_1_10634 5 243 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 269 (accept_3_2 4 243 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 269 (Polychromatic418967fa.accept_21_3_12_17_1_7471 3 243
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 269 (accept_3_2 1 243 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243
  269))))))))))))))))))))))))))) (allB_succ' 28 242 269 (Eq.refl Bool.true) (allA_succ_of_accept 27 242 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 242 269 (Polychromatic418967fa.accept_17_9_4_14_1_4302 26 242 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 242 269 (accept_3_2 25 242 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 242 269 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 242 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 242 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 242 269 (accept_3_2 22 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 242 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 242 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 242 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 242 269 (accept_3_2 19 242 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 242 269 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 242 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 242 269
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 242 269 (accept_3_2 16 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 242 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 242 269 (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 242 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 242 269 (accept_3_2 13 242 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 242 269 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 242
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 242 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 242 269 (accept_3_2 10 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  242 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 242 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 242 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 242 269 (accept_3_2 7 242 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 242 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 242 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 242 269
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 242 269 (accept_3_2 4 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  242 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 242 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 242 269 (Polychromatic418967fa.accept_18_2_8_17_1_4754 2 242 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 242 269 (accept_3_2 1 242 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 242 269)))))))))))))))))))))))))))) (allB_succ' 29 241 269 (Eq.refl
  Bool.true) (allA_of_3_0 29 241 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 240 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 240 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 240 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 240 269 (accept_3_2 28 240 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 240 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 240 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 240 269 (Polychromatic418967fa.accept_7_5_2_3_1_106
  26 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 240 269 (accept_3_2 25
  240 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 240 269
  (Polychromatic418967fa.accept_21_3_9_17_1_2983 24 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 240 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 240 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 240 269 (accept_3_2 22 240 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 240 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 240 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 240 269 (Polychromatic418967fa.accept_7_6_2_3_1_107
  20 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 240 269 (accept_3_2 19
  240 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 240 269
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 240 269 (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 240 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 240 269 (accept_3_2 16 240 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 240 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 240 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 240 269 (Polychromatic418967fa.accept_9_5_6_8_1_101
  14 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 240 269 (accept_3_2 13
  240 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 240 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 240 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 240 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 240 269 (accept_3_2 10 240 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 240 269 (Polychromatic418967fa.accept_19_9_12_3_1_2950 9 240 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 240 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 240 269 (accept_3_2 7 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  240 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 240 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 240 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 240 269 (accept_3_2 4 240 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 240 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 240 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 240 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 240 269 (accept_3_2 1 240 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240
  269)))))))))))))))))))))))))))))) (allB_succ' 31 239 269 (Eq.refl Bool.true) (allA_succ_of_accept 30 239 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 239 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 239 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 239 269 (accept_3_2 28 239 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 239 269 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 239 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 239 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 239 269 (accept_3_2 25 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 239 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 239 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 239 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 239 269 (accept_3_2 22 239 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 239 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 239 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 239 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 239 269 (accept_3_2 19 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 239 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 239 269 (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 239 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 239 269 (accept_3_2 16 239 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 239 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 239 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 239 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 239 269 (accept_3_2 13 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 239 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 239 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 239 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 239 269 (accept_3_2 10 239 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 239 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 239 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 239 269
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 8 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 239 269 (accept_3_2 7 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  239 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 239 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 239 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 269 (accept_3_2 4 239 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 239 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 239 269 (accept_3_2 1 239 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239
  269))))))))))))))))))))))))))))))) (allB_succ' 32 238 269 (Eq.refl Bool.true) (allA_of_3_0 32 238 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 237 269 (Eq.refl Bool.true) (allA_succ_of_accept 32 237 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 237 269 (accept_3_2 31 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 237 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 237 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 237 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 237 269 (accept_3_2 28 237 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 237 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 237 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 237 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 237 269 (accept_3_2 25 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 237 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 237 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 237 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 269 (accept_3_2 22 237 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 269 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 237 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 237 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 237 269 (accept_3_2 19 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 237 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 237 269 (Polychromatic418967fa.accept_15_2_12_14_1_1709 17 237 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 269 (accept_3_2 16 237 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 237 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 237 269 (accept_3_2 13 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 237 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 237 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 237 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 269 (accept_3_2 10 237 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 237 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 269 (accept_3_2 7 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  237 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 237 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 237 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 269 (accept_3_2 4 237 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 237 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 269 (accept_3_2 1 237 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237
  269))))))))))))))))))))))))))))))))) (allB_succ' 34 236 269 (Eq.refl Bool.true) (allA_succ_of_accept 33 236 269
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 236 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 236 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 236 269 (accept_3_2 31 236 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 236 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 236 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 236 269 (Polychromatic418967fa.accept_7_1_5_3_1_268
  29 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 236 269 (accept_3_2 28
  236 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 236 269
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 236 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 236 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 236 269 (accept_3_2 25 236 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 236 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 236 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 236 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 236 269 (accept_3_2 22
  236 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 236 269
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 236 269 (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 236 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 236 269 (accept_3_2 19 236 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 236 269 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 236 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 236 269
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 236 269 (accept_3_2 16 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 236 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 236 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 236 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 236 269 (accept_3_2 13 236 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 236 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 236 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 236 269
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 236 269 (accept_3_2 10 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  236 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 236 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 236 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 236 269 (accept_3_2 7 236 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 236 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 236 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 236 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 236 269 (accept_3_2 4 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  236 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 236 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 236 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 236 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 236 269 (accept_3_2 1 236 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 236 269)))))))))))))))))))))))))))))))))) (allB_succ' 35 235 269 (Eq.refl Bool.true)
  (allA_of_3_0 35 235 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 234 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 234 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 234 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 234 269 (accept_3_2 34 234 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 234 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 234 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 234 269
  (Polychromatic418967fa.accept_23_9_4_16_1_16464 32 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 234 269 (accept_3_2 31 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 234 269 (Polychromatic418967fa.accept_11_8_3_5_1_355 30 234 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 234 269 (Polychromatic418967fa.accept_21_8_3_17_1_7399 29 234
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 234 269 (accept_3_2 28 234
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 234 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 234 269 (Polychromatic418967fa.accept_19_7_6_3_1_6998 26 234 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 234 269 (accept_3_2 25 234 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 234 269 (Polychromatic418967fa.accept_19_5_6_3_1_5578 24 234 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 234 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 234 269 (accept_3_2 22 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 234 269 (Polychromatic418967fa.accept_14_7_10_3_1_1034 21 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 234 269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 234 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 234 269 (accept_3_2 19 234 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 234 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 234
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 234 269
  (Polychromatic418967fa.accept_19_17_6_3_1_9830 17 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 234 269 (accept_3_2 16 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 234 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 234 269 (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 234 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 234 269 (accept_3_2 13 234 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 234 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 234
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 234 269 (accept_3_2 10 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  234 269 (Polychromatic418967fa.accept_19_9_6_3_1_5563 9 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 234 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 234 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 234 269 (accept_3_2 7 234 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 234 269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 234 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 234 269
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 234 269 (accept_3_2 4 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  234 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 234 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 234 269 (Polychromatic418967fa.accept_19_2_6_3_1_4182 2 234 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 234 269 (accept_3_2 1 234 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 234 269)))))))))))))))))))))))))))))))))))) (allB_succ' 37 233 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 233 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 233 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 233 269 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 233
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 233 269 (accept_3_2 34 233
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 233 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 233 269 (Polychromatic418967fa.accept_17_15_12_14_1_2087 32 233 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 233 269 (accept_3_2 31 233 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 233 269 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 233 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 233 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 233 269 (accept_3_2 28 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 233 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 233 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 233 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 233 269 (accept_3_2 25 233 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 233 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 233 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 233 269
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 233 269 (accept_3_2 22 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 233 269 (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 233 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 233 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 233 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 269 (accept_3_2 19 233 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 269
  (Polychromatic418967fa.accept_22_18_13_5_1_16463 18 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 233 269 (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 233 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 269 (accept_3_2 16 233 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 233 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 233 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 269
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 233 269 (accept_3_2 13 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 233 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 233 269 (Polychromatic418967fa.accept_17_11_12_14_1_5431 11 233 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 269 (accept_3_2 10 233 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 269 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 233
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 269 (accept_3_2 7 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 233 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 269 (accept_3_2 4 233 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 269 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 233 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 269
  (Polychromatic418967fa.accept_19_2_5_3_1_5536 2 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 269 (accept_3_2 1 233 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  269))))))))))))))))))))))))))))))))))))) (allB_succ' 38 232 269 (Eq.refl Bool.true) (allA_of_3_0 38 232 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 231 269 (Eq.refl Bool.true) (allA_succ_of_accept 38 231 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 231 269 (accept_3_2 37 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 231 269 (Polychromatic418967fa.accept_16_4_7_13_1_2795 36 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 231 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 231 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 231 269 (accept_3_2 34 231 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 231 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 231
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 231 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 231 269 (accept_3_2 31 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 231 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 231 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 231 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 269 (accept_3_2 28 231 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 231 269 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 231 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 231 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 231 269 (accept_3_2 25 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 231 269 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 231 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 231 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 269 (accept_3_2 22 231 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 231 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 269 (accept_3_2 19 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 231 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 231 269 (Polychromatic418967fa.accept_22_17_11_5_1_14910 17 231 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 269 (accept_3_2 16 231 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 231
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 269 (accept_3_2 13 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 231 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 231 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 231 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 269 (accept_3_2 10 231 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 231 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 269 (accept_3_2 7 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  231 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 231 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 231 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 269 (accept_3_2 4 231 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 231 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 269 (accept_3_2 1 231 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  269))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 230 269 (Eq.refl Bool.true) (allA_succ_of_accept 39 230 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 230 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 230 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 230 269 (accept_3_2 37 230 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 230 269 (Polychromatic418967fa.accept_15_6_5_14_1_429 36 230 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 230 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 230 269 (accept_3_2 34 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 230 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 230 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 230 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 230 269 (accept_3_2 31 230 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 230 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 230 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 230 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 230 269 (accept_3_2 28 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 230 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 230 269 (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 230 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 230 269 (accept_3_2 25 230 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 230 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 230 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 230 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 230 269 (accept_3_2 22 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 230 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 230 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 230 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 230 269 (accept_3_2 19 230 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 230 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 230 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 230 269
  (Polychromatic418967fa.accept_11_6_10_5_1_341 17 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 230 269 (accept_3_2 16 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 230 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 230 269 (Polychromatic418967fa.accept_21_14_20_17_1_15009 14 230 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 230 269 (accept_3_2 13 230 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 230 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 230 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 230 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 230 269 (accept_3_2 10 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  230 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 230 269 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 230 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 230 269 (accept_3_2 7 230 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 230 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 230 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 230 269
  (Polychromatic418967fa.accept_17_5_9_14_1_4282 5 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 230 269 (accept_3_2 4 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  230 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 230 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 230 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 230 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 230 269 (accept_3_2 1 230 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 230 269)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 229 269 (Eq.refl
  Bool.true) (allA_of_3_0 41 229 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 228 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 228 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 228 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 228 269 (accept_3_2 40 228 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 228 269 (Polychromatic418967fa.accept_16_7_4_13_1_1057 39 228 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 228 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 228 269 (accept_3_2 37 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 228 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 228 269 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 228 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 228 269 (accept_3_2 34 228 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 228 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 228 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 228 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 228 269 (accept_3_2 31 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 228 269 (Polychromatic418967fa.accept_13_4_7_9_1_5260 30 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 228 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 228 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 228 269 (accept_3_2 28 228 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 228 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 228 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 228 269
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 228 269 (accept_3_2 25 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 228 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 228 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 228 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 228 269 (accept_3_2 22 228 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 228 269 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 228 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 228 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 228 269 (accept_3_2 19 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 228 269 (Polychromatic418967fa.accept_23_18_21_16_1_16462 18 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 228 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 228 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 269 (accept_3_2 16 228 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 228 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 228 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 228 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 228 269 (accept_3_2 13 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 228 269 (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 228 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 228 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 269 (accept_3_2 10 228 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 228 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 228 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 228 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 228 269 (accept_3_2 7 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  228 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 228 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 228 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 228 269 (accept_3_2 4 228 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 228 269 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 228 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 228 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 228 269 (accept_3_2 1 228 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  269)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 227 269 (Eq.refl Bool.true) (allA_succ_of_accept 42 227
  269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 227 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 227 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 227 269 (accept_3_2 40 227 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 227 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 227 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 227 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38
  227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 227 269 (accept_3_2 37
  227 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 227 269
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 227 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 227 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 227 269 (accept_3_2 34 227 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 227 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 227 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 227 269 (Polychromatic418967fa.accept_9_5_2_8_1_109
  32 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 227 269 (accept_3_2 31
  227 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 227 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 227 269 (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 227 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 227 269 (accept_3_2 28 227 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 227 269 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 227 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 227 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 227 269 (accept_3_2 25 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 227 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 227 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 227 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 227 269 (accept_3_2 22 227 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 227 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 227 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 227 269
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 227 269 (accept_3_2 19 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 227 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 227 269 (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 227 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 269 (accept_3_2 16 227 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 227 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 227 269 (accept_3_2 13 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 227 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 227 269 (Polychromatic418967fa.accept_19_11_18_3_1_1755 11 227 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 269 (accept_3_2 10 227 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 269 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 227 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 269
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 227 269 (accept_3_2 7 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  227 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 227 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 227 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 269 (accept_3_2 4 227 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 227 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 269 (accept_3_2 1 227 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  269))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 226 269 (Eq.refl Bool.true) (allA_of_3_0 44 226 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 225 269 (Eq.refl Bool.true) (allA_succ_of_accept 44 225 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 225 269 (accept_3_2 43 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 225 269 (Polychromatic418967fa.accept_19_4_16_3_1_4175 42 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 225 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 225 269 (accept_3_2 40 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 225 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 225 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 225 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 225 269 (accept_3_2 37 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 225 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 225 269 (Polychromatic418967fa.accept_16_3_1_13_1_4968 35 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 225 269 (accept_3_2 34 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 225 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 225 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 225 269 (accept_3_2 31 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 225 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 225 269 (Polychromatic418967fa.accept_21_8_15_17_1_4382 29 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 269 (accept_3_2 28 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 225
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 225 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 225 269 (accept_3_2 25 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 225 269 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 225 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 225 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 269 (accept_3_2 22 225 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 225 269 (accept_3_2 19 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 225 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 225 269 (Polychromatic418967fa.accept_19_17_16_3_1_8401 17 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 269 (accept_3_2 16 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 225
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 269 (accept_3_2 13 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 225 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 225 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 225 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 269 (accept_3_2 10 225 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 269 (accept_3_2 7 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  225 269 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 225 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 225 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 269 (accept_3_2 4 225 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 225 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 269 (accept_3_2 1 225 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  269))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 224 269 (Eq.refl Bool.true) (allA_succ_of_accept 45
  224 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 224 269 (Polychromatic418967fa.accept_13_5_3_9_1_1189 44 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 224 269 (accept_3_2 43 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 224 269 (Polychromatic418967fa.accept_20_2_4_9_1_9524 42 224
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 224 269
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 41 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 224 269 (accept_3_2 40 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 224 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 224 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 224 269 (accept_3_2 37 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 224 269 (Polychromatic418967fa.accept_17_2_3_14_1_8043 36 224
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 224 269
  (Polychromatic418967fa.accept_10_5_4_9_1_420 35 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 224 269 (accept_3_2 34 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 224 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 224 269 (Polychromatic418967fa.accept_11_10_4_5_1_359 32 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 224 269 (accept_3_2 31 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 224 269 (Polychromatic418967fa.accept_21_9_14_17_1_12039 30
  224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 224 269
  (Polychromatic418967fa.accept_19_10_15_3_1_5470 29 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 224 269 (accept_3_2 28 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 224 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 224 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 224 269 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 224
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 224 269 (accept_3_2 25 224
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 224 269
  (Polychromatic418967fa.accept_21_3_14_17_1_10628 24 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 224 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 224 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 224 269 (accept_3_2 22 224 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 224 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 224 269
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 20 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 224 269 (accept_3_2 19 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 224 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 224 269 (Polychromatic418967fa.accept_19_17_15_3_1_4174 17 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 224 269 (accept_3_2 16 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 224 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 224 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 224 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 224 269 (accept_3_2 13 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 224 269 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 224 269 (Polychromatic418967fa.accept_17_11_3_14_1_6736 11 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 224 269 (accept_3_2 10 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 224 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 224 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 224 269
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 224 269 (accept_3_2 7 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  224 269 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 224 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 224 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 269 (accept_3_2 4 224 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 224 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 224 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 224 269 (accept_3_2 1 224 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  269)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 223 269 (Eq.refl Bool.true) (allA_of_3_0 47 223 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 222 269 (Eq.refl Bool.true) (allA_succ_of_accept 47 222 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 222 269 (accept_3_2 46 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 222 269 (Polychromatic418967fa.accept_13_6_1_9_1_619 45 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 222 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 222 269 (accept_3_2 43 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 222 269 (Polychromatic418967fa.accept_16_10_14_13_1_1870 42 222 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 222 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 222 269 (accept_3_2 40 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 222 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 222 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 222 269 (accept_3_2 37 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 222 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 222 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 222 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 222 269 (accept_3_2 34 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 222 269 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 222 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 222 269 (accept_3_2 31 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 222 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 222 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 222 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 222 269 (accept_3_2 28 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 222 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 222 269 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 222 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 222 269 (accept_3_2 25 222 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 222 269 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 222
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 222 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 222 269 (accept_3_2 22 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 222 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 222 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 222 269 (accept_3_2 19 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 222 269 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 222 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 222 269
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 222 269 (accept_3_2 16 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 222 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 222 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 269 (accept_3_2 13 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 222 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 222 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 222 269
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 222 269 (accept_3_2 10 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  222 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 222 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 269 (accept_3_2 7 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 269 (Polychromatic418967fa.accept_13_6_1_9_1_619 6 222 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 222 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 222 269 (accept_3_2 4 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  222 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 222 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 222 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 269 (accept_3_2 1 222 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 222 269)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 221 269 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 221 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 221 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 221 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 47
  221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 221 269 (accept_3_2 46
  221 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 221 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 221 269 (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 221 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 221 269 (accept_3_2 43 221 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 221 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 221 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 221 269 (Polychromatic418967fa.accept_7_6_4_3_1_266
  41 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 221 269 (accept_3_2 40
  221 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 221 269
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 221 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 221 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 221 269 (accept_3_2 37 221 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 221 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 221 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 221 269 (Polychromatic418967fa.accept_10_5_1_9_1_791
  35 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 221 269 (accept_3_2 34
  221 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 221 269
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 221 269 (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 221 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 221 269 (accept_3_2 31 221 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 221 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 221 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 221 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 29
  221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 269 (accept_3_2 28
  221 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 221 269 (Polychromatic418967fa.accept_18_8_5_17_1_1388 26 221 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 221 269 (accept_3_2 25 221 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 221 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 221 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 221 269
  (Polychromatic418967fa.accept_21_2_11_17_1_4395 23 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 221 269 (accept_3_2 22 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 221 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 221 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 221 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 269 (accept_3_2 19 221 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 221 269 (Polychromatic418967fa.accept_10_8_1_9_1_413
  18 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 269
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 221 269 (accept_3_2 16 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 221 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 221 269 (Polychromatic418967fa.accept_25_14_21_19_1_7626 14 221 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 269 (accept_3_2 13 221 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 221 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 221 269 (accept_3_2 10 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  221 269 (Polychromatic418967fa.accept_19_9_12_3_1_2950 9 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 221 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 221 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 269 (accept_3_2 7 221 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 221 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 269 (accept_3_2 4 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 221 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 221 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 269 (accept_3_2 1 221 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 221 269))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 220 269
  (Eq.refl Bool.true) (allA_of_3_0 50 220 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 219 269 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 219 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 219 269 (accept_3_2 49 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 219 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 219 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 219 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 219 269 (accept_3_2 46 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 219 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 219 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 269 (accept_3_2 43 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 219 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 219 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 219 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 219 269 (accept_3_2 40 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 219 269 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 219 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 269 (accept_3_2 37 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 219 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 219 269
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 219 269 (accept_3_2 34 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 219 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 219 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 269 (accept_3_2 31 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 219 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 219 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 219 269 (accept_3_2 28 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 219 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 219 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 269 (accept_3_2 25 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 219 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 219 269 (accept_3_2 22 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 219 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 219 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 269 (accept_3_2 19 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 219 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 269
  (Polychromatic418967fa.accept_11_6_10_5_1_341 17 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 269 (accept_3_2 16 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 219 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 219 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 269 (accept_3_2 13 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 219 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 269 (accept_3_2 10 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  219 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 219 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 269 (accept_3_2 7 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 219 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 269 (accept_3_2 4 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 269 (Polychromatic418967fa.accept_17_3_15_14_1_4219 3 219 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 269 (accept_3_2 1 219 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 219 269))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 218 269
  (Eq.refl Bool.true) (allA_succ_of_accept 51 218 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 218 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 218 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 218 269 (accept_3_2 49 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 218 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 218 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 218 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 218 269 (accept_3_2 46 218 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 218 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 218 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 218 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 218 269 (accept_3_2 43 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 218 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 218 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 218 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 218 269 (accept_3_2 40 218 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 218 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 218 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 218 269
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 38 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 218 269 (accept_3_2 37 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 218 269 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 218 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 218 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 218 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 218 269 (accept_3_2 34 218 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 218 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 218 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 218 269 (accept_3_2 31 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 218 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 218 269 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 218 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 218 269 (accept_3_2 28 218 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 218 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 218 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 218 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 218 269 (accept_3_2 25 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 218 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 218 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 218 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 218 269 (accept_3_2 22 218 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 218 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 218 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 218 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 218 269 (accept_3_2 19 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 218 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 218 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 218 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 218 269 (accept_3_2 16 218 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 218 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 218 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 218 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 218 269 (accept_3_2 13 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 218 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 218 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 218 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 218 269 (accept_3_2 10 218 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 218 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 218 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 218 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 218 269 (accept_3_2 7 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  218 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 218 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 218 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 218 269 (accept_3_2 4 218 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 218 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 218 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 218 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 218 269 (accept_3_2 1 218 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  269)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 217 269 (Eq.refl Bool.true) (allA_of_3_0 53 217
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 216 269 (Eq.refl Bool.true) (allA_succ_of_accept 53 216
  269 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 216 269 (accept_3_2 52 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 216 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 216 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 216 269 (Polychromatic418967fa.accept_13_11_8_9_1_1161 50 216
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 216 269 (accept_3_2 49 216
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 216 269
  (Polychromatic418967fa.accept_19_10_7_3_1_6977 48 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 216 269 (Polychromatic418967fa.accept_20_7_16_9_1_4970 47 216 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 216 269 (accept_3_2 46 216 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 216 269 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 216 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 216 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 216 269 (accept_3_2 43 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 216 269 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 216 269 (Polychromatic418967fa.accept_37_4_31_10_1_16461 41 216 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 216 269 (accept_3_2 40 216 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 216 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 216 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 216 269
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 38 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 216 269 (accept_3_2 37 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 216 269 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 216 269 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 216 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 216 269 (accept_3_2 34 216 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 216 269 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 216
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 216 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 216 269 (accept_3_2 31 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 216 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 216 269 (Polychromatic418967fa.accept_13_3_8_9_1_1134 29 216 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 216 269 (accept_3_2 28 216 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 216 269 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 216
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 216 269
  (Polychromatic418967fa.accept_17_9_12_14_1_5423 26 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 216 269 (accept_3_2 25 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 216 269 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 216 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 216 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 216 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 269 (accept_3_2 22 216 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 216 269
  (Polychromatic418967fa.accept_16_5_8_13_1_2764 21 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 216 269 (Polychromatic418967fa.accept_11_9_7_5_1_749 20 216 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 216 269 (accept_3_2 19 216 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 216 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 216 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 216 269 (Polychromatic418967fa.accept_13_4_8_9_1_1156
  17 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 216 269 (accept_3_2 16
  216 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 216 269
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 216 269 (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 216 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 269 (accept_3_2 13 216 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 216 269 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 216 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 216 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 216 269 (accept_3_2 10 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  216 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 216 269 (Polychromatic418967fa.accept_15_8_6_14_1_975 8 216 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 269 (accept_3_2 7 216 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 216 269 (Polychromatic418967fa.accept_19_6_7_3_1_1733 6 216 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 269
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 216 269 (accept_3_2 4 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  216 269 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 216 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 216 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 216 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 269 (accept_3_2 1 216 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 216 269)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 215 269
  (Eq.refl Bool.true) (allA_succ_of_accept 54 215 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 215 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 215 269
  (Polychromatic418967fa.accept_15_8_5_14_1_986 53 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 215 269 (accept_3_2 52 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 215 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 215 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 215 269 (accept_3_2 49 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 215 269 (Polychromatic418967fa.accept_22_4_17_5_1_14920 48 215 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 215 269
  (Polychromatic418967fa.accept_13_8_7_9_1_611 47 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 215 269 (accept_3_2 46 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 215 269 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 215 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 215 269 (accept_3_2 43 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 215 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 215 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 215 269
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 215 269 (accept_3_2 40 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 215 269 (Polychromatic418967fa.accept_15_9_5_14_1_973 39 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 215 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 269 (accept_3_2 37 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 215 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 215 269
  (Polychromatic418967fa.accept_19_16_6_3_1_6972 35 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 215 269 (accept_3_2 34 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 215 269 (Polychromatic418967fa.accept_17_16_11_14_1_4213 33 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 269 (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 215 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 269 (accept_3_2 31 215 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 215 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 215 269 (accept_3_2 28 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 215 269 (Polychromatic418967fa.accept_19_8_6_3_1_4164 27 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 215 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 269 (accept_3_2 25 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 215 269 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 215 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 215 269 (accept_3_2 22 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 215 269 (Polychromatic418967fa.accept_16_4_7_13_1_2795 20 215 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 269 (accept_3_2 19 215 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 215 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 269
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 269 (accept_3_2 16 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 215 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 215 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 269 (accept_3_2 13 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 269 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 215 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 269
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 269 (accept_3_2 10 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 269 (accept_3_2 7 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 215 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 269
  (Polychromatic418967fa.accept_19_5_6_3_1_5578 5 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 269 (accept_3_2 4 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 269 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 215 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 269 (accept_3_2 1 215 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 269))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 214 269
  (Eq.refl Bool.true) (allA_of_3_0 56 214 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 213 269 (Eq.refl
  Bool.true) (allA_succ_of_accept 56 213 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 269 (accept_3_2 55 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 213 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 213 269
  (Polychromatic418967fa.accept_13_1_5_9_1_226 53 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 213 269 (accept_3_2 52 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 213 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 213 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 269 (accept_3_2 49 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 213 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 213 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 213 269 (accept_3_2 46 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 213 269 (Polychromatic418967fa.accept_18_9_15_17_1_3497 45 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 213 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 269 (accept_3_2 43 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 269 (Polychromatic418967fa.accept_13_3_5_9_1_5285 42 213 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 213 269 (accept_3_2 40 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 213 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 213 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 269 (accept_3_2 37 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 269 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 213 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 269
  (Polychromatic418967fa.accept_19_16_4_3_1_2946 35 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 213 269 (accept_3_2 34 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 213 269 (Polychromatic418967fa.accept_16_1_5_13_1_1025 33 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 213 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 269 (accept_3_2 31 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 213 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 269 (accept_3_2 28 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 213 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 213 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 269 (accept_3_2 25 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 213 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 269 (accept_3_2 22 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 213 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 213 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 269 (accept_3_2 19 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 269 (Polychromatic418967fa.accept_16_2_5_13_1_3842 18 213 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 269
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 269 (accept_3_2 16 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 213 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 213 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 269 (accept_3_2 13 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 213 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 269 (accept_3_2 10 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 269 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 269 (accept_3_2 7 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 269 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 213 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 269 (accept_3_2 4 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 213 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 269 (accept_3_2 1 213 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 212 269
  (Eq.refl Bool.true) (allA_succ_of_accept 57 212 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 212 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 212 269 (accept_3_2 55 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 212 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 212 269 (Polychromatic418967fa.accept_21_11_2_17_1_2975 53 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 212 269 (accept_3_2 52 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 212 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 212 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 212 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 212 269 (accept_3_2 49 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 212 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 212 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 212 269 (accept_3_2 46 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 212 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 212 269
  (Polychromatic418967fa.accept_13_5_4_9_1_601 44 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 212 269 (accept_3_2 43 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 212 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 212 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 212 269 (accept_3_2 40 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 212 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 212 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 212 269 (accept_3_2 37 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 212 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 212 269 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 212 269 (accept_3_2 34 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 212 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 212 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 212 269
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 32 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 212 269 (accept_3_2 31 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 212 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 212 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 212 269 (accept_3_2 28 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 212 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 212 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 212 269 (accept_3_2 25 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 212 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 212 269 (Polychromatic418967fa.accept_16_7_4_13_1_1057 23 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 212 269 (accept_3_2 22 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 212 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 212 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 212 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 212 269 (accept_3_2 19 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 212 269 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 212 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 212 269 (accept_3_2 16 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 212 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 212 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 212 269 (accept_3_2 13 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 212 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 212 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 212 269 (accept_3_2 10 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 212 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 212 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 212 269 (accept_3_2 7 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  212 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 212 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 212 269 (accept_3_2 4 212 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 212 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 212 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 212 269 (accept_3_2 1 212 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 211 269 (Eq.refl Bool.true) (allA_of_3_0
  59 211 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 210 269 (Eq.refl Bool.true) (allA_succ_of_accept 59
  210 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 210 269 (accept_3_2 58 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 210 269 (Polychromatic418967fa.accept_13_5_2_9_1_1195 57 210 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 210 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 210 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 210 269 (accept_3_2 55 210 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 210 269
  (Polychromatic418967fa.accept_17_3_6_14_1_4312 54 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 210 269 (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 210 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 210 269 (accept_3_2 52 210 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 210 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 210 269 (Polychromatic418967fa.accept_9_5_3_8_1_316
  50 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 210 269 (accept_3_2 49
  210 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 210 269
  (Polychromatic418967fa.accept_19_10_1_3_1_12548 48 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 210 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 210 269 (accept_3_2 46 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 210 269 (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 210 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 210 269
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 44 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 210 269 (accept_3_2 43 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 210 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 210 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 210 269 (accept_3_2 40 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 210 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 210 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 210 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 210 269 (accept_3_2 37 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 210 269 (Polychromatic418967fa.accept_19_17_1_3_1_4160 36 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 210 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 210 269 (accept_3_2 34 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 210 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 210 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 210 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 210 269 (accept_3_2 31 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 210 269 (Polychromatic418967fa.accept_19_11_1_3_1_5555 30 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 210 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 210 269 (accept_3_2 28 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 210 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 210 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 210 269
  (Polychromatic418967fa.accept_20_6_10_9_1_3486 26 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 210 269 (accept_3_2 25 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 210 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 210 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 210 269 (accept_3_2 22 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 210 269 (Polychromatic418967fa.accept_16_5_2_13_1_1007 21 210 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 210 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 210 269 (accept_3_2 19 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 210 269 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 210 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 210 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 269 (accept_3_2 16 210 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 210 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 210 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 210 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 210 269 (accept_3_2 13 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 210 269 (Polychromatic418967fa.accept_24_12_18_5_1_16397 12 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 210 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 210 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 269 (accept_3_2 10 210 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 210 269 (Polychromatic418967fa.accept_18_9_12_17_1_6060 9 210
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 269
  (Polychromatic418967fa.accept_17_8_6_14_1_6718 8 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 210 269 (accept_3_2 7 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  210 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 210 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 269 (accept_3_2 4 210 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 210 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 210 269 (accept_3_2 1 210 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 209 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 209 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 209 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 209 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 209 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 209 269 (accept_3_2 58 209 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 209 269 (Polychromatic418967fa.accept_9_3_2_8_1_108
  57 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 209 269
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 56 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 209 269 (accept_3_2 55 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 209 269 (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 209 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 209 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 209 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 209 269 (accept_3_2 52 209 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 209 269 (Polychromatic418967fa.accept_7_2_6_3_1_100
  51 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 209 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 209 269 (accept_3_2 49 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 209 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 209 269 (Polychromatic418967fa.accept_13_8_1_9_1_1178 47 209 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 209 269 (accept_3_2 46 209 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 209 269 (Polychromatic418967fa.accept_13_6_1_9_1_619 45 209
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 209 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 209 269 (accept_3_2 43 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 209 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 209 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 209 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 209 269 (accept_3_2 40 209 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 209 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 209 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 269
  (Polychromatic418967fa.accept_14_10_13_3_1_2552 38 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 209 269 (accept_3_2 37 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 209 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 209 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 269 (Polychromatic418967fa.accept_16_3_1_13_1_4968 35 209
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 209 269 (accept_3_2 34 209
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 209 269
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 209 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 209 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 269 (accept_3_2 31 209 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 209 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 209 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 269
  (Polychromatic418967fa.accept_21_8_20_17_1_7455 29 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 209 269 (accept_3_2 28 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 209 269 (Polychromatic418967fa.accept_17_10_5_14_1_4203 27 209 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 269
  (Polychromatic418967fa.accept_17_9_5_14_1_4277 26 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 209 269 (accept_3_2 25 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 209 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 209 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 209 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 269 (accept_3_2 22 209 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 209 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 209 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 269
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 209 269 (accept_3_2 19 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 209 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 209 269 (Polychromatic418967fa.accept_22_17_11_5_1_14910 17 209 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 269 (accept_3_2 16 209 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 209 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 269 (accept_3_2 13 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 209 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 269 (accept_3_2 10 209 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 209 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 269
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 8 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 269 (accept_3_2 7 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 209 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 269 (accept_3_2 4 209 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 209 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 269 (accept_3_2 1 209 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 208 269 (Eq.refl Bool.true)
  (allA_of_3_0 62 208 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 207 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 207 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 207 269 (accept_3_2 61 207 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 207 269 (Polychromatic418967fa.accept_13_8_12_9_1_1168 60 207 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 207 269
  (Polychromatic418967fa.accept_19_2_17_3_1_11224 59 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 207 269 (accept_3_2 58 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 207 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 207 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 207 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 207 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 269 (accept_3_2 55 207 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 207 269
  (Polychromatic418967fa.accept_17_2_3_14_1_8043 53 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 207 269 (accept_3_2 52 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 207 269 (Polychromatic418967fa.accept_11_7_9_5_1_338 51 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 269 (accept_3_2 49 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 207 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 207 269
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 47 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 269 (accept_3_2 46 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 207 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 207 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 269 (accept_3_2 43 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 207 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 207 269 (accept_3_2 40 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 207 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 269 (accept_3_2 37 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 207 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 269
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 35 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 269 (accept_3_2 34 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 207 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 207 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 269 (accept_3_2 31 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 207 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 207 269 (accept_3_2 28 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 207 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 269 (accept_3_2 25 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 207 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 269
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 207 269 (accept_3_2 22 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 207 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 207 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 207 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 269 (accept_3_2 19 207 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 269
  (Polychromatic418967fa.accept_15_2_12_14_1_1709 17 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 207 269 (accept_3_2 16 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 207 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 207 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 207 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 269 (accept_3_2 13 207 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 269 (Polychromatic418967fa.accept_10_2_7_9_1_783
  12 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 269
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 207 269 (accept_3_2 10 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 207 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 207 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 269 (accept_3_2 7 207 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 269
  (Polychromatic418967fa.accept_19_5_17_3_1_4152 5 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 269 (accept_3_2 4 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 269 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 207 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 269 (accept_3_2 1 207 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 207 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  206 269 (Eq.refl Bool.true) (allA_succ_of_accept 63 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 206 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 206 269
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 62 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 206 269 (accept_3_2 61 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 206 269 (Polychromatic418967fa.accept_13_8_11_9_1_593 60 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 206 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 206 269 (accept_3_2 58 206 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 206 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 206 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 206 269 (accept_3_2 55 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 206 269 (Polychromatic418967fa.accept_13_2_11_9_1_591 54 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 206 269 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 206 269 (accept_3_2 52 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 206 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 206 269
  (Polychromatic418967fa.accept_17_16_2_14_1_6715 50 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 206 269 (accept_3_2 49 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 206 269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 206 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 206 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 206 269 (accept_3_2 46 206 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 206 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 206 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 206 269 (accept_3_2 43 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 206 269 (Polychromatic418967fa.accept_15_12_11_14_1_3464 42 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 206 269 (Polychromatic418967fa.accept_13_2_11_9_1_591 41 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 206 269 (accept_3_2 40 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 206 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 206 269
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 38 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 206 269 (accept_3_2 37 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 206 269 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 206 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 206 269 (accept_3_2 34 206 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 206 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 206 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 206 269 (accept_3_2 31 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 206 269 (Polychromatic418967fa.accept_20_10_6_9_1_4989 30 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 206 269 (Polychromatic418967fa.accept_23_6_22_16_1_16460 29 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 206 269 (accept_3_2 28 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 206 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 206 269
  (Polychromatic418967fa.accept_16_10_14_13_1_1870 26 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 206 269 (accept_3_2 25 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 206 269 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 206 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 206 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 206 269 (accept_3_2 22 206 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 206 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 206 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 206 269 (accept_3_2 19 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 206 269 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 206 269 (Polychromatic418967fa.accept_16_1_14_13_1_3834 17 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 206 269 (accept_3_2 16 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 206 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 206 269
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 206 269 (accept_3_2 13 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 206 269 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 269 (accept_3_2 10 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 206 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 206 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 206 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 206 269 (accept_3_2 7 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  206 269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 206 269 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 206 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 269 (accept_3_2 4 206 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 206 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 269
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 269 (accept_3_2 1 206 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 205 269 (Eq.refl Bool.true)
  (allA_of_3_0 65 205 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 204 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 204 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 204 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 204 269 (accept_3_2 64 204 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 204 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 204 269
  (Polychromatic418967fa.accept_19_5_14_3_1_4187 62 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 204 269 (accept_3_2 61 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 204 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 204 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 204 269 (accept_3_2 58 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 204 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 204 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 204 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 204 269 (accept_3_2 55 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 204 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 204 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 204 269 (accept_3_2 52 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 204 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 204 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 204 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 204 269 (accept_3_2 49 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 204 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 204 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 204 269 (accept_3_2 46 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 204 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 204 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 204 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 204 269 (accept_3_2 43 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 204 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 42 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 204 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 204 269 (accept_3_2 40 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 204 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 204 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 204 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 204 269 (accept_3_2 37 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 204 269 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 204 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 204 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 204 269 (accept_3_2 34 204 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 204 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 204 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 204 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 204 269 (accept_3_2 31 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 204 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 204 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 204 269 (accept_3_2 28 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 204 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 204 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 204 269 (accept_3_2 25 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 204 269 (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 204 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 204 269 (accept_3_2 22 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 204 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 204 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 269
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 204 269 (accept_3_2 19 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 204 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 204 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 204 269 (accept_3_2 16 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 204 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 204 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 269
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 204 269 (accept_3_2 13 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 204 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 204 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 269 (accept_3_2 10 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 204 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 204 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 269
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 204 269 (accept_3_2 7 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  204 269 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 204 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 204 269 (accept_3_2 4 204 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 204 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 204 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 204 269 (accept_3_2 1 204 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 203 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 203 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 203 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 203 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 203 269 (accept_3_2 64 203 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 203 269
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 203 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 203 269 (accept_3_2 61 203 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 203 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 203 269 (Polychromatic418967fa.accept_13_7_8_9_1_1158
  59 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 203 269 (accept_3_2 58
  203 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 203 269
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 203 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 203 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 203 269 (accept_3_2 55 203 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 203 269 (Polychromatic418967fa.accept_13_1_8_9_1_1154
  53 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 203 269 (accept_3_2 52
  203 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 203 269
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 203 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 203 269 (accept_3_2 49 203 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 203 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 203 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 47
  203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 203 269 (accept_3_2 46
  203 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 203 269
  (Polychromatic418967fa.accept_17_11_16_14_1_6760 45 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 203 269 (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 203 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 203 269 (accept_3_2 43 203 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 203 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 203 269
  (Polychromatic418967fa.accept_21_20_14_17_1_10643 41 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 203 269 (accept_3_2 40 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 203 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 203 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 203 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 269 (accept_3_2 37 203 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 203 269 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  36 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 269
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 203 269 (accept_3_2 34 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 203 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 203 269 (Polychromatic418967fa.accept_14_4_7_3_1_1718 32 203 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 269 (accept_3_2 31 203 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 203 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 203 269 (accept_3_2 28 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 203 269 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 269 (accept_3_2 25 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 203 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 269
  (Polychromatic418967fa.accept_19_4_13_3_1_5571 23 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 269 (accept_3_2 22 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 269 (accept_3_2 19 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 203 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 269
  (Polychromatic418967fa.accept_13_4_8_9_1_1156 17 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 269 (accept_3_2 16 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 269 (accept_3_2 13 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 203 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 203 269 (accept_3_2 10 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  203 269 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 203 269 (Polychromatic418967fa.accept_16_8_11_13_1_7265 8 203 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 269 (accept_3_2 7 203 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 203 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 269
  (Polychromatic418967fa.accept_15_5_8_14_1_432 5 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 269 (accept_3_2 4 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 203 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 269 (accept_3_2 1 203 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 202 269 (Eq.refl Bool.true) (allA_of_3_0 68 202 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 201 269
  (Eq.refl Bool.true) (allA_succ_of_accept 68 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 201 269 (accept_3_2 67 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 201 269 (Polychromatic418967fa.accept_13_1_6_9_1_1197 66 201
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 201 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 201 269 (accept_3_2 64 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 201 269 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 201 269 (accept_3_2 61 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 201 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 201 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 201 269 (accept_3_2 58 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 201 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 269 (accept_3_2 55 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 269 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 201 269
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 53 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 201 269 (accept_3_2 52 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 201 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 269 (accept_3_2 49 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 201 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 201 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 201 269 (accept_3_2 46 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 201 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 269 (accept_3_2 43 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 201 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 201 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 201 269 (accept_3_2 40 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 201 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 269 (accept_3_2 37 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 201 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 201 269 (accept_3_2 34 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 201 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 269 (accept_3_2 31 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 201 269 (accept_3_2 28 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 201 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 269 (accept_3_2 25 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 201 269 (accept_3_2 22 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 201 269 (Polychromatic418967fa.accept_16_5_9_13_1_3845 21 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 269 (accept_3_2 19 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 269 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 269
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 201 269 (accept_3_2 16 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 201 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 269 (accept_3_2 13 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 269 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 269 (accept_3_2 10 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  201 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 269 (accept_3_2 7 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 201 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 269 (accept_3_2 4 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 201 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 269 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 269 (accept_3_2 1 201 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 200 269 (Eq.refl Bool.true) (allA_succ_of_accept 69 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32
  69 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 200 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 200 269 (accept_3_2 67 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 200 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 200 269 (Polychromatic418967fa.accept_18_11_2_17_1_3490 65 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 200 269 (accept_3_2 64 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 200 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 200 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 200 269 (accept_3_2 61 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 200 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 200 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 200 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 200 269 (accept_3_2 58 200 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 200 269
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 56 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 200 269 (accept_3_2 55 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 200 269 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 200 269 (Polychromatic418967fa.accept_13_1_5_9_1_226 53 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 200 269 (accept_3_2 52 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 200 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 200 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 200 269 (accept_3_2 49 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 200 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 200 269 (Polychromatic418967fa.accept_15_2_5_14_1_61 47 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 200 269 (accept_3_2 46 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 200 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 200 269
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 44 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 200 269 (accept_3_2 43 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 200 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 200 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 200 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 200 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 200 269 (accept_3_2 40 200 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39
  200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 200 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 200 269 (accept_3_2 37 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 200 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 200 269 (Polychromatic418967fa.accept_14_7_4_3_1_488 35 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 200 269 (accept_3_2 34 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 200 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 200 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 200 269 (accept_3_2 31 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 200 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 200 269 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 200 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 200 269 (accept_3_2 28 200 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 200 269 (accept_3_2 25 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 200 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 200 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 200 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 269 (accept_3_2 22 200 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 200 269
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 200 269 (accept_3_2 19 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 200 269 (Polychromatic418967fa.accept_17_1_13_14_1_478 18 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 200 269 (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 200 269 (accept_3_2 16 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 200 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 200 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 200 269 (accept_3_2 13 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 200 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 200 269 (Polychromatic418967fa.accept_16_11_8_13_1_3844 11 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 200 269 (accept_3_2 10 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 269
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 200 269 (accept_3_2 7 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  200 269 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 200 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 200 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 269 (accept_3_2 4 200 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 269 (accept_3_2 1 200 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 199 269 (Eq.refl Bool.true)
  (allA_of_3_0 71 199 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 198 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 198 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 198 269 (accept_3_2 70 198 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 198 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 198 269 (Polychromatic418967fa.accept_7_5_2_3_1_106
  68 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 198 269 (accept_3_2 67
  198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 198 269
  (Polychromatic418967fa.accept_21_3_9_17_1_2983 66 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 198 269 (Polychromatic418967fa.accept_21_2_9_17_1_4376 65 198 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 198 269 (accept_3_2 64 198 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 198 269 (Polychromatic418967fa.accept_7_6_2_3_1_107
  62 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 198 269 (accept_3_2 61
  198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 198 269
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 60 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 198 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 198 269 (accept_3_2 58 198 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 198 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 198 269
  (Polychromatic418967fa.accept_15_11_3_14_1_971 56 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 198 269 (accept_3_2 55 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 198 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 198 269 (Polychromatic418967fa.accept_19_15_8_3_1_13786 53 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 198 269 (accept_3_2 52 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 198 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 198 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 198 269 (accept_3_2 49 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 198 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 198 269 (accept_3_2 46 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 198 269 (Polychromatic418967fa.accept_13_6_3_9_1_1827 45 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 198 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 44 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 198 269 (accept_3_2 43 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 198 269 (Polychromatic418967fa.accept_17_8_11_14_1_6770 42 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 198 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 198 269 (accept_3_2 40 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 198 269
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 38 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 198 269 (accept_3_2 37 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 198 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 198 269 (accept_3_2 34 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 198 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 198 269
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 32 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 198 269 (accept_3_2 31 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 198 269 (Polychromatic418967fa.accept_19_11_8_3_1_862 30 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 198 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 198 269 (accept_3_2 28 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 198 269 (accept_3_2 25 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 198 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 198 269 (accept_3_2 22 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 198 269 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 198 269 (accept_3_2 19 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 198 269 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 198 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 198 269 (accept_3_2 16 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 198 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 198 269 (accept_3_2 13 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 198 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 198 269 (accept_3_2 10 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 269 (Polychromatic418967fa.accept_16_9_6_13_1_3831 9 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 198 269 (accept_3_2 7 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  198 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 198 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 198 269 (accept_3_2 4 198 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 198 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 198 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 269
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 2 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 198 269 (accept_3_2 1 198 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 197 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 197 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 197 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 197 269 (Polychromatic418967fa.accept_13_6_2_9_1_1188 71 197
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 197 269 (accept_3_2 70 197
  269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 197 269
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 69 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 197 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 197 269 (accept_3_2 67 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 197 269 (Polychromatic418967fa.accept_13_1_2_9_1_1186 66 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 197 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 197 269 (accept_3_2 64 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 197 269 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 197 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 62 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 197 269 (accept_3_2 61 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 197 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 197 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 197 269
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 59 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 197 269 (accept_3_2 58 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 197 269 (Polychromatic418967fa.accept_13_5_2_9_1_1195 57 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 197 269 (Polychromatic418967fa.accept_16_8_5_13_1_1021 56 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 197 269 (accept_3_2 55 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 197 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 197 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 197 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 197 269 (accept_3_2 52 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 197 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 197 269 (Polychromatic418967fa.accept_11_6_10_5_1_341 50 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 197 269 (accept_3_2 49 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 197 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 197
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 197 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 197 269 (accept_3_2 46 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 197 269 (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 197 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 197 269 (accept_3_2 43 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 197 269 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 197 269
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 41 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 197 269 (accept_3_2 40 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 197 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 197 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 38 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 197 269 (accept_3_2 37 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 197 269 (Polychromatic418967fa.accept_21_15_8_17_1_7436 36 197
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 197 269
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 197 269 (accept_3_2 34 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 197 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 197 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 197 269 (accept_3_2 31 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 197 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 197 269
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 197 269 (accept_3_2 28 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 197 269 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 197 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 269 (accept_3_2 25 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 197 269 (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 197 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 269
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 197 269 (accept_3_2 22 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 197 269 (Polychromatic418967fa.accept_25_21_22_19_1_16459 21 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 269 (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 269 (accept_3_2 19 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 197 269 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 197 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 269
  (Polychromatic418967fa.accept_11_6_10_5_1_341 17 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 197 269 (accept_3_2 16 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 197 269 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 269 (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 269 (accept_3_2 13 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 269 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 197 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 269
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 269 (accept_3_2 10 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 269 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 269 (accept_3_2 7 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 269 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 197 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 269
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 269 (accept_3_2 4 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 269 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 197 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 269 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 269 (accept_3_2 1 197 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 74 196 269 (Eq.refl Bool.true) (allA_of_3_0 74 196 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 75 195 269 (Eq.refl Bool.true) (allA_succ_of_accept 74 195 269 (Polychromatic418967fa.accept_4_2_3_1_1_2
  74 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 195 269 (accept_3_2 73
  195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 195 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 195 269 (Polychromatic418967fa.accept_10_1_5_9_1_157 71 195 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 195 269 (accept_3_2 70 195 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 195 269 (Polychromatic418967fa.accept_11_3_8_5_1_336 69 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 195 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 195 269 (accept_3_2 67 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 195 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 195 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 195 269 (accept_3_2 64 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 195 269 (Polychromatic418967fa.accept_16_15_3_13_1_2818 63 195 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 195 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 195 269 (accept_3_2 61 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 195 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 195 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 195 269 (accept_3_2 58 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 195 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 195 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 195 269 (accept_3_2 55 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 195 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 195 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 269 (accept_3_2 52 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 195 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 195 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 195 269 (accept_3_2 49 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 195 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 195 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 269 (accept_3_2 46 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 195 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 195 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 195 269 (accept_3_2 43 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 195 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 195 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 269 (accept_3_2 40 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 195 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 195 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 195 269 (accept_3_2 37 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 195 269 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 195 269 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 269 (accept_3_2 34 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 269 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 195
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 195 269 (accept_3_2 31 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 195 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 195 269 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 269 (accept_3_2 28 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 269 (Polychromatic418967fa.accept_18_9_15_17_1_3497 27 195 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 195 269 (accept_3_2 25 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 195 269 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 195 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 269 (accept_3_2 22 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 269 (accept_3_2 19 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 195 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 195 269 (Polychromatic418967fa.accept_16_1_3_13_1_2785 17 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 269 (accept_3_2 16 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 269 (Polychromatic418967fa.accept_16_15_3_13_1_2818 15 195
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 195 269 (accept_3_2 13 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 195 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 195 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 269 (accept_3_2 10 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 269 (accept_3_2 7 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  195 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 195 269 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 269 (accept_3_2 4 195 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 269 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 195 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 269
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 269 (accept_3_2 1 195 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 194 269 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 194 269 (Polychromatic418967fa.accept_9_2_5_8_1_11 74
  194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 194 269 (accept_3_2 73
  194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 194 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 194 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 194 269 (accept_3_2 70 194 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 194 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 194 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  68 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 194 269 (accept_3_2 67
  194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 194 269
  (Polychromatic418967fa.accept_9_3_5_8_1_99 66 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 194 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 194 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 194 269 (accept_3_2 64 194 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 194 269
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 62 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 194 269 (accept_3_2 61 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 194 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 194 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 194 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 194 269 (accept_3_2 58 194 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 194 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57
  194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 194 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 194 269 (accept_3_2 55 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 194 269 (Polychromatic418967fa.accept_19_16_4_3_1_2946 54 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 194 269 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 194 269 (accept_3_2 52 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 194 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 194 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 194 269 (accept_3_2 49 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 194 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 194 269 (accept_3_2 46 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 194 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 194 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 194 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 194 269 (accept_3_2 43 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 194 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 194 269 (Polychromatic418967fa.accept_24_17_2_5_1_16446 41 194 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 194 269 (accept_3_2 40 194 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 194 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 194 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 194 269 (accept_3_2 37 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 194 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 194 269 (accept_3_2 34 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 194 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 194 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 194 269
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 194 269 (accept_3_2 31 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 194 269 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 194 269 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 269 (accept_3_2 28 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 194 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 194 269
  (Polychromatic418967fa.accept_19_7_4_3_1_5533 26 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 194 269 (accept_3_2 25 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 194 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 194 269 (accept_3_2 22 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 194 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 194 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 194 269
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 194 269 (accept_3_2 19 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 194 269 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 194 269 (Polychromatic418967fa.accept_22_17_18_5_1_16458 17 194 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 194 269 (accept_3_2 16 194 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 194 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 194 269
  (Polychromatic418967fa.accept_21_14_5_17_1_16409 14 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 194 269 (accept_3_2 13 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 194 269 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 194 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 194 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 269 (accept_3_2 10 194 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9
  194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 269
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 269 (accept_3_2 7 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 269 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 269 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 269 (accept_3_2 4 194 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 269 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 194 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 269
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 269 (accept_3_2 1 194 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 193 269 (Eq.refl
  Bool.true) (allA_of_3_0 77 193 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 192 269 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 192 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 192 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 192 269 (accept_3_2 76 192 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 192 269 (Polychromatic418967fa.accept_19_18_2_3_1_4177 75 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 192 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 192 269 (accept_3_2 73 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 192 269 (Polychromatic418967fa.accept_21_9_3_17_1_4365 72 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 192 269 (Polychromatic418967fa.accept_10_1_2_9_1_152 71 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 192 269 (accept_3_2 70 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 192 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 192 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 192 269 (accept_3_2 67 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 192 269 (Polychromatic418967fa.accept_13_1_10_9_1_215 66 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 192 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 192 269 (accept_3_2 64 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 192 269 (Polychromatic418967fa.accept_14_7_10_3_1_1034 63 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 192 269
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 62 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 192 269 (accept_3_2 61 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 192 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 192 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 192 269 (accept_3_2 58 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 192 269 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 192 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 192 269 (accept_3_2 55 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 192 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 54 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 192 269 (Polychromatic418967fa.accept_13_1_10_9_1_215 53 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 192 269 (accept_3_2 52 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 192 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 192 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 192 269 (accept_3_2 49 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 192 269 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 192 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 192 269 (accept_3_2 46 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 192 269 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 192 269
  (Polychromatic418967fa.accept_17_10_5_14_1_4203 44 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 192 269 (accept_3_2 43 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 192 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 192 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 192 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 269 (accept_3_2 40 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 192 269
  (Polychromatic418967fa.accept_15_9_12_14_1_963 39 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 192 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 192 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 192 269 (accept_3_2 37 192 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 192 269 (Polychromatic418967fa.accept_17_2_5_14_1_2068 36 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 192 269
  (Polychromatic418967fa.accept_14_7_10_3_1_1034 35 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 192 269 (accept_3_2 34 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 192 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 192 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 192 269 (accept_3_2 31 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 192 269 (Polychromatic418967fa.accept_19_11_2_3_1_8424 30 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 192 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 192 269 (accept_3_2 28 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 192 269 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 192 269 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 269 (accept_3_2 25 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 192 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 192 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 192 269 (accept_3_2 22 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 192 269 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 192 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 192 269 (accept_3_2 19 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 192 269 (Polychromatic418967fa.accept_19_18_2_3_1_4177 18 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 192 269
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 192 269 (accept_3_2 16 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 192 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 192 269 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 269 (accept_3_2 13 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 269 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 269
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 192 269 (accept_3_2 10 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  192 269 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 192 269 (Polychromatic418967fa.accept_21_8_3_17_1_7399 8 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 269 (accept_3_2 7 192 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 192 269 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 192 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 269
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 192 269 (accept_3_2 4 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  192 269 (Polychromatic418967fa.accept_20_3_12_9_1_6410 3 192 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 192 269 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 269 (accept_3_2 1 192 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 192 269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 191 269 (Eq.refl Bool.true) (allA_succ_of_accept 78 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2
  78 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 191 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 191 269 (accept_3_2 76 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 191 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 191 269 (accept_3_2 73 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 191 269 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 191 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 191 269 (accept_3_2 70 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 191 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 191 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 191 269 (accept_3_2 67 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 191 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 65 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 191 269 (accept_3_2 64 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 191 269 (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 191 269 (accept_3_2 61 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 191 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 191 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 191 269 (accept_3_2 58 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 191 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 191 269 (Polychromatic418967fa.accept_18_2_11_17_1_4773 56 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 191 269 (accept_3_2 55 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 191 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 191 269
  (Polychromatic418967fa.accept_21_11_2_17_1_2975 53 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 191 269 (accept_3_2 52 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 191 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 191 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 191 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 191 269 (accept_3_2 49 191 269
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 191 269 (Polychromatic418967fa.accept_7_6_2_3_1_107
  48 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 191 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 191 269 (accept_3_2 46 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 191 269 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 191 269 (Polychromatic418967fa.accept_16_12_15_13_1_3872 44 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 191 269 (accept_3_2 43 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 191 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 269
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 191 269 (accept_3_2 40 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 191 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 269 (accept_3_2 37 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 269
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 269 (accept_3_2 34 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 269 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 269 (accept_3_2 31 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 269
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 269 (accept_3_2 28 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 269 (accept_3_2 25 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 269 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 269
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 269 (accept_3_2 22 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 269 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 269 (accept_3_2 19 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 269
  (Polychromatic418967fa.accept_19_17_1_3_1_4160 17 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 269 (accept_3_2 16 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 269 (accept_3_2 13 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 269 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 269
  (Polychromatic418967fa.accept_19_11_1_3_1_5555 11 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 269 (accept_3_2 10 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 269 (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 269 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 269 (accept_3_2 7 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 191 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 269
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 269 (accept_3_2 4 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 269 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 191 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 269 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 269 (accept_3_2 1 191 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 269)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 190 269 (Eq.refl Bool.true) (allA_of_3_0 80 190 269 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 81 189 269 (Eq.refl Bool.true) (allA_succ_of_accept 80 189 269 (Polychromatic418967fa.accept_6_2_3_5_1_26
  80 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 189 269 (accept_3_2 79
  189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 189 269
  (Polychromatic418967fa.accept_19_2_18_3_1_5517 78 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 189 269 (Polychromatic418967fa.accept_22_11_13_5_1_7084 77 189 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 189 269 (accept_3_2 76 189 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 189 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 189 269 (accept_3_2 73 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 189 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 72 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 189 269 (Polychromatic418967fa.accept_13_6_7_9_1_1848 71 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 189 269 (accept_3_2 70 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 189 269 (Polychromatic418967fa.accept_13_4_7_9_1_5260 69 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 189 269 (accept_3_2 67 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 189 269 (Polychromatic418967fa.accept_14_10_7_3_1_1022 66 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 189 269 (Polychromatic418967fa.accept_15_5_9_14_1_1724 65 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 269 (accept_3_2 64 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 189 269 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 189 269 (accept_3_2 61 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 189 269 (Polychromatic418967fa.accept_13_8_7_9_1_611 60 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 189 269 (Polychromatic418967fa.accept_19_2_18_3_1_5517 59 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 269 (accept_3_2 58 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 189 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 189 269 (accept_3_2 55 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 189 269 (Polychromatic418967fa.accept_13_2_7_9_1_2616 54 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 189 269 (Polychromatic418967fa.accept_14_11_7_3_1_3416 53 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 269 (accept_3_2 52 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 189 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 189 269 (accept_3_2 49 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 189 269 (Polychromatic418967fa.accept_18_12_9_17_1_7428 48 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 189 269 (Polychromatic418967fa.accept_13_8_7_9_1_611 47 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 269 (accept_3_2 46 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 189 269 (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 189 269 (accept_3_2 43 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 189 269 (Polychromatic418967fa.accept_13_3_7_9_1_1153 42 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 189 269 (Polychromatic418967fa.accept_11_8_2_5_1_1769 41 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 269 (accept_3_2 40 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 189 269 (accept_3_2 37 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 189 269 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 189 269 (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 269 (accept_3_2 34 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 269 (Polychromatic418967fa.accept_17_16_2_14_1_6715 33 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 189 269 (accept_3_2 31 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 189 269 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 189 269 (Polychromatic418967fa.accept_13_3_7_9_1_1153 29 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 269 (accept_3_2 28 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 189 269 (accept_3_2 25 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 189 269 (Polychromatic418967fa.accept_13_11_7_9_1_612 24 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 189 269 (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 269 (accept_3_2 22 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 269 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 269 (accept_3_2 19 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 189 269 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 189 269 (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 269 (accept_3_2 16 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 269 (accept_3_2 13 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 189 269 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 269 (Polychromatic418967fa.accept_13_11_7_9_1_612 11 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 269 (accept_3_2 10 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 269 (Polychromatic418967fa.accept_19_9_18_3_1_5475 9 189
  269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 269 (accept_3_2 7 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  189 269 (Polychromatic418967fa.accept_13_6_7_9_1_1848 6 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 189 269 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 269 (accept_3_2 4 189 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 269 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 189 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 269
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 269 (accept_3_2 1 189 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 188 269 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 188 269 (Polychromatic418967fa.accept_13_2_6_9_1_2636
  80 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 188 269 (accept_3_2 79
  188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 188 269
  (Polychromatic418967fa.accept_17_10_1_14_1_489 78 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 188 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 77 188 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 188 269 (accept_3_2 76 188 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 188 269 (Polychromatic418967fa.accept_7_4_6_3_1_271
  74 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 188 269 (accept_3_2 73
  188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 188 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 188 269 (Polychromatic418967fa.accept_10_1_8_9_1_787 71 188 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 188 269 (accept_3_2 70 188 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 188 269 (Polychromatic418967fa.accept_13_3_6_9_1_1150
  68 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 188 269 (accept_3_2 67
  188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 188 269
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 66 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 188 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 188 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 188 269 (accept_3_2 64 188 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 188 269 (Polychromatic418967fa.accept_12_2_8_5_1_408
  62 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 188 269 (accept_3_2 61
  188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 188 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 188 269 (Polychromatic418967fa.accept_13_7_6_9_1_1831 59 188 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 188 269 (accept_3_2 58 188 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 188 269 (Polychromatic418967fa.accept_13_4_6_9_1_3401
  56 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 188 269 (accept_3_2 55
  188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 188 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 188 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 188 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 188 269 (accept_3_2 52 188 269 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 188 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388
  50 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 188 269 (accept_3_2 49
  188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 188 269
  (Polychromatic418967fa.accept_22_4_12_5_1_11851 48 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 188 269 (Polychromatic418967fa.accept_10_7_8_9_1_785 47 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 188 269 (accept_3_2 46 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 188 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 188 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 188 269 (accept_3_2 43 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 188 269 (Polychromatic418967fa.accept_13_3_6_9_1_1150 42 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 188 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 188 269 (accept_3_2 40 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 188 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 188 269 (accept_3_2 37 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 188 269 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 188 269 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 188 269 (accept_3_2 34 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 188 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 188 269
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 188 269 (accept_3_2 31 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 188 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 188 269 (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 188 269 (accept_3_2 28 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 188 269
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 188 269
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 188 269 (accept_3_2 25 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 188 269 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 188 269 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 188 269 (accept_3_2 22 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 188 269
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 20 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 188 269 (accept_3_2 19 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 188 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 188 269 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 188 269 (accept_3_2 16 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 188 269
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 188 269 (accept_3_2 13 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 188 269 (Polychromatic418967fa.accept_19_12_17_3_1_5515 12 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 188 269 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 188 269 (accept_3_2 10 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 188 269
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 8 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 188 269 (accept_3_2 7 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  188 269 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 188 269 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 188 269 (accept_3_2 4 188 269 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 188 269 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 269 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 269
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 188 269 (accept_3_2 1 188 269 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  269))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_269_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


