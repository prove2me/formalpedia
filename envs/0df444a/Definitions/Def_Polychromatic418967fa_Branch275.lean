-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch275
-- name    : Polychromatic418967fa_Branch275
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:32:20.909355+00:00
-- url     : https://prove2.me/theorems/4eb019e7-bcaf-44bb-ac59-6581b00e0db8
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch275_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_275 : allB 275 275 :=
  allB_succ' 2 274 275 (Eq.refl Bool.true) (allA_of_3_0 2 274 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  273 275 (Eq.refl Bool.true) (allA_succ_of_accept 2 273 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 273 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 273 275 (accept_3_2 1 273 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 273 275))) (allB_succ' 4 272 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 272 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 272 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 272 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 272 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 272 275 (accept_3_2 1 272 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 272 275)))) (allB_succ' 5 271 275 (Eq.refl Bool.true) (allA_of_3_0
  5 271 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 270 275 (Eq.refl Bool.true) (allA_succ_of_gcd 5 270
  275 5 1 54 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4
  270 275 (accept_3_2 4 270 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 270 275
  (Polychromatic418967fa.accept_13_3_10_2_1_381 3 270 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 270 275 (Polychromatic418967fa.accept_14_2_4_9_1_2121 2 270 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 270 275 (accept_3_2 1 270 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 270 275)))))) (allB_succ' 7 269 275 (Eq.refl Bool.true) (allA_succ_of_accept 6 269 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 269 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 269 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 269 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 269 275 (accept_3_2 4 269 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 269 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 269 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 269 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2
  269 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 269 275 (accept_3_2 1 269
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 269 275))))))) (allB_succ' 8 268 275 (Eq.refl Bool.true)
  (allA_of_3_0 8 268 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 267 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 267 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 267 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 267 275 (accept_3_2 7 267 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 267 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 267 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 267 275 (Polychromatic418967fa.accept_13_5_7_2_1_852 5
  267 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 267 275 (accept_3_2 4 267
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 267 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 267 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 267 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 267 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 275 (accept_3_2 1 267 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 267 275))))))))) (allB_succ' 10 266 275 (Eq.refl Bool.true) (allA_succ_of_accept 9 266 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 266 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 266 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 266 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 266 275 (accept_3_2 7 266 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 266 275 (Polychromatic418967fa.accept_15_6_11_5_1_168 6 266 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 266 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  266 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 266 275 (accept_3_2 4 266
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 266 275 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 266 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 266 275
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 266 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 266 275 (accept_3_2 1 266 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 266
  275)))))))))) (allB_succ' 11 265 275 (Eq.refl Bool.true) (allA_of_3_0 11 265 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 264 275 (Eq.refl Bool.true) (allA_succ_of_gcd 11 264 275 11 1 24 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 264 275 (accept_3_2 10 264 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 264 275 (Polychromatic418967fa.accept_10_9_4_5_1_616 9
  264 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 264 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 264 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 264 275 (accept_3_2 7 264 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  264 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 264 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 264 275 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 264 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 264 275 (accept_3_2 4 264 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 264 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 264 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 264 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 264 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 264 275 (accept_3_2 1 264 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 264
  275)))))))))))) (allB_succ' 13 263 275 (Eq.refl Bool.true) (allA_succ_of_accept 12 263 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 263 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 263 275 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 263 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 263 275 (accept_3_2 10 263 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 263 275 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 263 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 263 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  263 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 263 275 (accept_3_2 7 263
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 263 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 263 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 263 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 263 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 263 275 (accept_3_2 4 263 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 263 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 263 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 263 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 2
  263 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 263 275 (accept_3_2 1 263
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 263 275))))))))))))) (allB_succ' 14 262 275 (Eq.refl Bool.true)
  (allA_of_3_0 14 262 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 261 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 14 261 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 261 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 261 275 (accept_3_2 13 261 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 261 275 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 261 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 261 275
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 261 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 261 275 (accept_3_2 10 261 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  261 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 261 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 261 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 261 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 261 275 (accept_3_2 7 261 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 261 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 261 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 261 275
  (Polychromatic418967fa.accept_17_5_6_3_1_4640 5 261 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 261 275 (accept_3_2 4 261 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  261 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 261 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 261 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 261 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 261 275 (accept_3_2 1 261 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 261 275))))))))))))))) (allB_succ' 16 260 275 (Eq.refl Bool.true) (allA_succ_of_gcd 15
  260 275 5 3 52 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 260 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 260 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 260 275 (accept_3_2 13 260 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 260 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 260 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 260 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 260 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 260 275 5 2 52 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 260 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 260 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 260 275 (Polychromatic418967fa.accept_16_8_4_3_1_3146 8 260 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 260 275 (accept_3_2 7 260 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 260 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 260 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 260 275 5 1 52 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 260 275 (accept_3_2 4 260 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 260 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 260 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 260 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 260 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 260 275 (accept_3_2 1 260 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 260
  275)))))))))))))))) (allB_succ' 17 259 275 (Eq.refl Bool.true) (allA_of_3_0 17 259 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 258 275 (Eq.refl Bool.true) (allA_succ_of_accept 17 258 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 258 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 258 275 (accept_3_2 16 258 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 258 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 258 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 258 275 (Polychromatic418967fa.accept_19_14_11_9_1_3330 14 258 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 258 275 (accept_3_2 13 258 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 258 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 258 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 258 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 258 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 258 275 (accept_3_2 10 258 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  258 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 258 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 258 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 258 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 258 275 (accept_3_2 7 258 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 258 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 258 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 258 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 258 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 258 275 (accept_3_2 4 258 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  258 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 258 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 258 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 258 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 258 275 (accept_3_2 1 258 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 258 275)))))))))))))))))) (allB_succ' 19 257 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 257 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 257 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 257 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 257 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 257 275 (accept_3_2 16 257 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 257 275
  (Polychromatic418967fa.accept_19_15_10_9_1_5956 15 257 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 257 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 257 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 257 275 (accept_3_2 13 257 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 257 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 257 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 257 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 257 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 257 275 (accept_3_2 10 257 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  257 275 (Polychromatic418967fa.accept_24_9_17_11_1_4810 9 257 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 257 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 257 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 257 275 (accept_3_2 7 257 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 257 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 257 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 257 275
  (Polychromatic418967fa.accept_13_5_10_2_1_856 5 257 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 257 275 (accept_3_2 4 257 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  257 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 257 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 257 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 257 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 257 275 (accept_3_2 1 257 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 257 275))))))))))))))))))) (allB_succ' 20 256 275 (Eq.refl Bool.true) (allA_of_3_0 20
  256 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 255 275 (Eq.refl Bool.true) (allA_succ_of_gcd 20 255
  275 5 4 51 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  255 275 (accept_3_2 19 255 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 255 275
  (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 255 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 255 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 255 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 255 275 (accept_3_2 16 255 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 255 275 5 3 51 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 255 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 255 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 255 275 (accept_3_2 13 255 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 255 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 255 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 255 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 255 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 255 275 5 2 51 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 255 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 255 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 255 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 255 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 255 275 (accept_3_2 7 255 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 255 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  255 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 255 275 5 1 51 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 255 275 (accept_3_2 4
  255 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 275
  (Polychromatic418967fa.accept_22_3_13_11_1_9138 3 255 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 255 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 255 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 275 (accept_3_2 1 255 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 255 275))))))))))))))))))))) (allB_succ' 22 254 275 (Eq.refl Bool.true) (allA_succ_of_accept 21
  254 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 254 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 254 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 254 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 254 275 (accept_3_2 19 254 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 254 275 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 254
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 254 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 254 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 254 275 (accept_3_2 16 254 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 254 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 254 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 254 275 (Polychromatic418967fa.accept_22_14_12_11_1_9182 14 254 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 254 275 (accept_3_2 13 254 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 254 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 254 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 254 275
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 254 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 254 275 (accept_3_2 10 254 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  254 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 254 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 254 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 254 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 254 275 (accept_3_2 7 254 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 254 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 254 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 254 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 254 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 254 275 (accept_3_2 4 254 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  254 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 254 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 254 275 (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 254 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 254 275 (accept_3_2 1 254 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 254 275)))))))))))))))))))))) (allB_succ' 23 253 275 (Eq.refl Bool.true)
  (allA_of_3_0 23 253 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 252 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 252 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 252 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 252 275 (accept_3_2 22 252 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 252 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 252 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 252 275
  (Polychromatic418967fa.accept_13_7_5_2_1_401 20 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 252 275 (accept_3_2 19 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 252 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 252 275 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 252 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 252 275 (accept_3_2 16 252 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 252 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 252 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 252 275
  (Polychromatic418967fa.accept_19_14_5_9_1_4596 14 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 252 275 (accept_3_2 13 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 252 275 (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 252 275 (Polychromatic418967fa.accept_17_11_14_3_1_1427 11 252 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 252 275 (accept_3_2 10 252 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 252 275 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 252 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 252 275
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 252 275 (accept_3_2 7 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  252 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 252 275 (Polychromatic418967fa.accept_20_5_12_15_1_9860 5 252 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 252 275 (accept_3_2 4 252 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 252 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 252 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 252 275
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 252 275 (accept_3_2 1 252 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252
  275)))))))))))))))))))))))) (allB_succ' 25 251 275 (Eq.refl Bool.true) (allA_succ_of_accept 24 251 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 251 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 251 275 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 251 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 251 275 (accept_3_2 22 251 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 251 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 251 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 251 275 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 251 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 251 275 (accept_3_2 19
  251 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 251 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 251 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 251 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 251 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 251 275 (accept_3_2 16 251 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 251 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 251 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 251 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018
  14 251 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 251 275 (accept_3_2 13
  251 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 251 275
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 251 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 251 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 251 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 251 275 (accept_3_2 10 251 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 251 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 251 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 251 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 8
  251 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 251 275 (accept_3_2 7 251
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 251 275
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 251 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 251 275 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 251 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 251 275 (accept_3_2 4 251 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 251 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 251 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 251 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  251 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 251 275 (accept_3_2 1 251
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 251 275))))))))))))))))))))))))) (allB_succ' 26 250 275
  (Eq.refl Bool.true) (allA_of_3_0 26 250 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 249 275 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 249 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 249 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 249 275 (accept_3_2 25 249 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 249 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 249 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 249 275
  (Polychromatic418967fa.accept_16_7_9_3_1_1324 23 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 249 275 (accept_3_2 22 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 249 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 249 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 249 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 249 275 (accept_3_2 19 249 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 249 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 249 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 249 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 249 275 (accept_3_2 16 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 249 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 249 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 249 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 275 (accept_3_2 13 249 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 249 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 249 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 249 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 249 275 (accept_3_2 10 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  249 275 (Polychromatic418967fa.accept_17_9_11_3_1_2353 9 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 249 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 249 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 275 (accept_3_2 7 249 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 249 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 249 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 249 275 (accept_3_2 4 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  249 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 249 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 249 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 249 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 275 (accept_3_2 1 249 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 249 275))))))))))))))))))))))))))) (allB_succ' 28 248 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 248 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 248 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 248 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 248 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 248 275 (accept_3_2 25 248 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 248 275
  (Polychromatic418967fa.accept_17_7_10_3_1_1421 24 248 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 248 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 248 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 248 275 (accept_3_2 22 248 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 248 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 248 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 248 275 (Polychromatic418967fa.accept_7_6_3_2_1_461
  20 248 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 248 275 (accept_3_2 19
  248 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 248 275
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 248 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 248 275 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 248 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 248 275 (accept_3_2 16 248 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 248 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 248 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 248 275 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 248 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 248 275 (accept_3_2 13
  248 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 248 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 248 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 248 275 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 248 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 248 275 (accept_3_2 10 248 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 248 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 248 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 248 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 8
  248 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 248 275 (accept_3_2 7 248
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 248 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 248 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 248 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 248 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 248 275 (accept_3_2 4 248 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 248 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 248 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 248 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  248 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 248 275 (accept_3_2 1 248
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248 275)))))))))))))))))))))))))))) (allB_succ' 29 247 275
  (Eq.refl Bool.true) (allA_of_3_0 29 247 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 246 275 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 246 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 246 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 246 275 (accept_3_2 28 246 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 246 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 246 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 246 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 246 275 (accept_3_2 25 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 246 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 246 275 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 246 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 246 275 (accept_3_2 22 246 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 246 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 246 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 246 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 246 275 (accept_3_2 19 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 246 275 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 246 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 246 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 246 275 (accept_3_2 16 246 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 246 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 246 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 246 275
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 246 275 (accept_3_2 13 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 246 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 246 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 246 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 246 275 (accept_3_2 10 246 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 246 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 246 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 246 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 246 275 (accept_3_2 7 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  246 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 246 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 246 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 246 275 (accept_3_2 4 246 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 246 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 246 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 246 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 246 275 (accept_3_2 1 246 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246
  275)))))))))))))))))))))))))))))) (allB_succ' 31 245 275 (Eq.refl Bool.true) (allA_succ_of_gcd 30 245 275 5 6 49 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 245 275
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 245 275 (accept_3_2 28 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 245 275 (Polychromatic418967fa.accept_17_10_7_3_1_727 27 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 245 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 245 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 245 275 5 5 49 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 245 275
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 245 275 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 245 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 245 275 (accept_3_2 22 245 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 245 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 245 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 245 275 5 4 49 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 245 275 (accept_3_2 19 245 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 245 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  245 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 245 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 245 275 (accept_3_2 16 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  245 275 5 3 49 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 245 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 245 275 (accept_3_2 13 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 245 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 245 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 245 275 (Polychromatic418967fa.accept_19_11_17_9_1_10138 11
  245 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 245 275 5 2 49 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 245 275
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 245 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 245 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 275 (accept_3_2 7 245 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 245 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 245 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 245 275 5 1 49 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 245 275 (accept_3_2 4 245 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 245 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 275 (accept_3_2 1 245 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245
  275))))))))))))))))))))))))))))))) (allB_succ' 32 244 275 (Eq.refl Bool.true) (allA_of_3_0 32 244 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 243 275 (Eq.refl Bool.true) (allA_succ_of_accept 32 243 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 243 275 (accept_3_2 31 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 243 275 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 243 275 (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 243 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 243 275 (accept_3_2 28 243 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 243 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 243
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 243 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 243 275 (accept_3_2 25 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 243 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 243 275 (Polychromatic418967fa.accept_15_8_3_5_1_608 23 243 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 275 (accept_3_2 22 243 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 243 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 243
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 243 275 (accept_3_2 19 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 243 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 243 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 243 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 275 (accept_3_2 16 243 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 275 (Polychromatic418967fa.accept_18_15_9_5_1_3934 15 243 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 243 275 (accept_3_2 13 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 243 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 243 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 243 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 275 (accept_3_2 10 243 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 243 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 243 275 (accept_3_2 7 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  243 275 (Polychromatic418967fa.accept_13_6_9_2_1_838 6 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 243 275 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 243 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 275 (accept_3_2 4 243 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 243 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 275 (accept_3_2 1 243 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243
  275))))))))))))))))))))))))))))))))) (allB_succ' 34 242 275 (Eq.refl Bool.true) (allA_succ_of_gcd 33 242 275 11 3 22
  25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 242 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 242 275 (accept_3_2 31 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 242 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 242 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 242 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 242 275 (accept_3_2 28 242 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 242 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 242 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 242 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 242 275 (accept_3_2 25 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 242 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 242 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 242 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 242 275 11 2 22 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 242 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 242 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 242 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 242 275 (accept_3_2 19 242 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 242 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 242 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 242 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 242 275 (accept_3_2 16 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 242 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 242 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 14 242 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 242 275 (accept_3_2 13 242 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 242 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 242 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 242 275 11 1 22 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 242 275 (accept_3_2 10
  242 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 242 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 242 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 242 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 242 275 (accept_3_2 7 242 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 242 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 242 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 242 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 242 275 (accept_3_2 4 242
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 242 275 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 242 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 242 275 (accept_3_2 1 242 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  275)))))))))))))))))))))))))))))))))) (allB_succ' 35 241 275 (Eq.refl Bool.true) (allA_of_3_0 35 241 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 240 275 (Eq.refl Bool.true) (allA_succ_of_gcd 35 240 275 5 7 48 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 240 275
  (accept_3_2 34 240 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 240 275
  (Polychromatic418967fa.accept_18_15_6_5_1_3972 33 240 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 240 275 (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 240 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 240 275 (accept_3_2 31 240 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 240 275 5 6 48 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 240 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 240 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 240 275 (accept_3_2 28 240 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 240 275 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 240
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 240 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 240 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 240 275 5 5 48 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 240 275 (Polychromatic418967fa.accept_19_5_12_9_1_4588 24 240 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 240 275 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 240
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 240 275 (accept_3_2 22 240
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 240 275
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 240 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 240 275 5 4 48 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 240 275 (accept_3_2 19 240 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 240 275 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 240 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 240 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 240 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 240 275 (accept_3_2 16 240 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 240 275 5 3 48 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 240 275 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 240 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 240 275 (accept_3_2 13 240 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 240 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12
  240 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 240 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 240 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 240 275 5 2 48 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 240 275 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 240 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 240 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 240 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 240 275 (accept_3_2 7 240 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 240 275 (Polychromatic418967fa.accept_21_6_9_2_1_9554
  6 240 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 240 275 5 1 48 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 240 275 (accept_3_2 4
  240 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 240 275
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 240 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 240 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 240 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 275 (accept_3_2 1 240 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 240 275)))))))))))))))))))))))))))))))))))) (allB_succ' 37 239 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 239 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 239 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 239 275 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 239
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 239 275 (accept_3_2 34 239
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 239 275
  (Polychromatic418967fa.accept_13_7_5_2_1_401 33 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 239 275 (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 239 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 239 275 (accept_3_2 31 239 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 239 275 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 239 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 239 275
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 239 275 (accept_3_2 28 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 239 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 239 275 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 239 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 239 275 (accept_3_2 25 239 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 239 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 239 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 239 275
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 239 275 (accept_3_2 22 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 239 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 239 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 239 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 239 275 (accept_3_2 19 239 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 239 275 (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 239 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 239 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 239 275 (accept_3_2 16 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 239 275 (Polychromatic418967fa.accept_17_15_1_3_1_1488 15 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 239 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 239 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 239 275 (accept_3_2 13 239 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 239 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 239 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 239 275 (accept_3_2 10 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  239 275 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 239 275 (Polychromatic418967fa.accept_14_8_1_9_1_2085 8 239 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 275 (accept_3_2 7 239 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 239 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 239 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 275
  (Polychromatic418967fa.accept_20_5_19_15_1_3946 5 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 239 275 (accept_3_2 4 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  239 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 239 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 239 275 (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 239 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 275 (accept_3_2 1 239 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 239 275))))))))))))))))))))))))))))))))))))) (allB_succ' 38 238 275 (Eq.refl
  Bool.true) (allA_of_3_0 38 238 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 237 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 237 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 237 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 237 275 (accept_3_2 37 237 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 237 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 237 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 237 275 (Polychromatic418967fa.accept_9_8_3_5_1_241
  35 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 237 275 (accept_3_2 34
  237 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 237 275
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 237 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 237 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 237 275 (accept_3_2 31 237 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 237 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 237 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 237 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 237 275 (accept_3_2 28
  237 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 237 275
  (Polychromatic418967fa.accept_12_3_9_11_1_231 27 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 237 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 237 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 237 275 (accept_3_2 25 237 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 237 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 237 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 237 275 (Polychromatic418967fa.accept_10_3_7_5_1_288
  23 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 275 (accept_3_2 22
  237 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 275
  (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 237 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 237 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 237 275 (accept_3_2 19 237 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 237 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 237 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 237 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 275 (accept_3_2 16
  237 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 237 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 237 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 275 (accept_3_2 13 237 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 237 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 237 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 237 275 (accept_3_2 10 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  237 275 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 237 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 237 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 275 (accept_3_2 7 237 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 237 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 237 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 275
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 237 275 (accept_3_2 4 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  237 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 237 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 237 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 237 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 275 (accept_3_2 1 237 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 237 275))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 236 275 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 236 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 236 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 236 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 236 275 (accept_3_2 37
  236 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 236 275
  (Polychromatic418967fa.accept_15_6_11_5_1_168 36 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 236 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 236 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 236 275 (accept_3_2 34 236 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 236 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 236 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 236 275 (Polychromatic418967fa.accept_7_4_5_2_1_243
  32 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 236 275 (accept_3_2 31
  236 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 236 275
  (Polychromatic418967fa.accept_9_3_2_5_1_234 30 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 236 275 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 236 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 236 275 (accept_3_2 28 236 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 236 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 236 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 236 275 (Polychromatic418967fa.accept_9_8_2_5_1_237
  26 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 236 275 (accept_3_2 25
  236 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 236 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 236 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 236 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 236 275 (accept_3_2 22 236 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 236 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 236 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 236 275
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 20 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 236 275 (accept_3_2 19 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 236 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 236 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 236 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 236 275 (accept_3_2 16 236 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 236 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 236 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 236 275
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 236 275 (accept_3_2 13 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 236 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 236 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 236 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 236 275 (accept_3_2 10 236 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 236 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 236 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 236 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 236 275 (accept_3_2 7 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  236 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 236 275 (Polychromatic418967fa.accept_20_5_16_15_1_3957 5 236 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 236 275 (accept_3_2 4 236 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 236 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 236 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 236 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 236 275 (accept_3_2 1 236 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  275)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 235 275 (Eq.refl Bool.true) (allA_of_3_0 41 235 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 234 275 (Eq.refl Bool.true) (allA_succ_of_accept 41 234 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 234 275 (accept_3_2 40 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 234 275 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 234 275 (Polychromatic418967fa.accept_17_4_13_3_1_7166 38 234 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 234 275 (accept_3_2 37 234 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 234 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 234 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 234 275
  (Polychromatic418967fa.accept_19_16_6_9_1_7335 35 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 234 275 (accept_3_2 34 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 234 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 234 275 (Polychromatic418967fa.accept_19_13_6_9_1_5989 32 234 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 234 275 (accept_3_2 31 234 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 234 275 (Polychromatic418967fa.accept_20_10_14_15_1_9885 30
  234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 234 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 234 275 (accept_3_2 28 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 234 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 234 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 234 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 234 275 (accept_3_2 25 234 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 234 275 (Polychromatic418967fa.accept_22_2_14_11_1_7450 24 234 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 234 275
  (Polychromatic418967fa.accept_16_7_10_3_1_2210 23 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 234 275 (accept_3_2 22 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 234 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 234 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 234 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 234 275 (accept_3_2 19 234 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 234 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 234 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 234 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 234 275 (accept_3_2 16 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 234 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 234 275 (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 234 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 234 275 (accept_3_2 13 234 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 234 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 234 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 275
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 234 275 (accept_3_2 10 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  234 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 234 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 234 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 234 275 (accept_3_2 7 234 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 234 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 234 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 234 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 234 275 (accept_3_2 4 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  234 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 234 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 234 275 (Polychromatic418967fa.accept_22_2_14_11_1_7450 2 234 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 234 275 (accept_3_2 1 234 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 234 275)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 233 275
  (Eq.refl Bool.true) (allA_succ_of_accept 42 233 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 233 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 233 275
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 233 275 (accept_3_2 40 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 233 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 233 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 233 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 233 275 (accept_3_2 37 233 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 233 275 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 233 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 233 275
  (Polychromatic418967fa.accept_27_8_17_5_1_16941 35 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 233 275 (accept_3_2 34 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 233 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 233 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 233 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 233
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 233 275 (accept_3_2 31 233
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 233 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 233 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 233 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 233 275 (accept_3_2 28 233 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 233 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 233 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 233 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 233 275 (accept_3_2 25 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 233 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 233 275 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 233 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 233 275 (accept_3_2 22 233 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 233 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 233 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 233 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 233 275 (accept_3_2 19 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 233 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 233 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 233 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 275 (accept_3_2 16 233 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 233 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 233 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 233 275 (accept_3_2 13 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 233 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 233 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 233 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 275 (accept_3_2 10 233 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 275 (Polychromatic418967fa.accept_22_9_13_11_1_2784 9 233 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 275
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 275 (accept_3_2 7 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 275 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 233 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 275 (accept_3_2 4 233 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 233 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 275 (accept_3_2 1 233 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  275))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 232 275 (Eq.refl Bool.true) (allA_of_3_0 44 232 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 231 275 (Eq.refl Bool.true) (allA_succ_of_gcd 44 231 275 11 4
  21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 231 275
  (accept_3_2 43 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 231 275
  (Polychromatic418967fa.accept_13_3_10_2_1_381 42 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 231 275 (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 231 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 231 275 (accept_3_2 40 231 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 231 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 231 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 231 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 38
  231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 231 275 (accept_3_2 37
  231 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 231 275
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 231 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 231 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 231 275 (accept_3_2 34 231 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 231 275 11 3 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 231 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 231 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 231 275 (accept_3_2 31 231 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 231 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 231 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 231 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 231 275 (accept_3_2 28 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 231 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 231 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 231 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 231 275 (accept_3_2 25 231 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 231 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 231 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 231 275
  (Polychromatic418967fa.accept_24_23_15_11_1_16940 23 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 231 275 11 2 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 231 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 231 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 275 (accept_3_2 19 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 231 275 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 231 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 231 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 275 (accept_3_2 16 231 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 275 (Polychromatic418967fa.accept_16_15_7_3_1_4273 15 231 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 275 (accept_3_2 13 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 231 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 231 275 11 1 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 10 231 275 (accept_3_2 10 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 231 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 231 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 231 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 275 (accept_3_2 7 231 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 231 275 (Polychromatic418967fa.accept_10_6_1_5_1_1024
  6 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 275
  (Polychromatic418967fa.accept_13_5_10_2_1_856 5 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 231 275 (accept_3_2 4 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  231 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 231 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 231 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 231 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 275 (accept_3_2 1 231 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 231 275))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 230 275 (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 230 275 5 9 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 230 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 230 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 230 275 (accept_3_2 43 230 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 230 275 (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 230
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 230 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 230 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 230 275 5 8 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 230 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 230 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 230 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 230 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 230 275 (accept_3_2 37 230 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 230 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36
  230 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 230 275 5 7 46 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 230 275 (accept_3_2 34
  230 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 230 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 230 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 230 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 230 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 230 275 (accept_3_2 31 230 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 230 275 5 6 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 230 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 230 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 230 275 (accept_3_2 28 230 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 230 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 230 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 230 275
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 26 230 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 230 275 5 5 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 230 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 230 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 230 275 (Polychromatic418967fa.accept_17_6_9_3_1_704 23 230
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 230 275 (accept_3_2 22 230
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 230 275 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 230 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 230 275 5 4 46 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 230 275
  (accept_3_2 19 230 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 230 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 230 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 230 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 230 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 230 275 (accept_3_2 16 230 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 230 275 5 3 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 230 275 (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 230 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 230 275 (accept_3_2 13 230 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 230 275 (Polychromatic418967fa.accept_19_12_2_9_1_15638 12 230
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 230 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 230 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 230 275 5 2 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 230 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 230 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 230 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 230 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 230 275 (accept_3_2 7 230 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 230 275 (Polychromatic418967fa.accept_13_6_9_2_1_838 6
  230 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 230 275 5 1 46 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 230 275 (accept_3_2 4
  230 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 230 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 230 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 230 275 (Polychromatic418967fa.accept_16_2_6_3_1_5396 2 230 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 230 275 (accept_3_2 1 230 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 230 275)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 229 275 (Eq.refl Bool.true)
  (allA_of_3_0 47 229 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 228 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 228 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 228 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 228 275 (accept_3_2 46 228 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 228 275 (Polychromatic418967fa.accept_18_9_12_5_1_864 45 228 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 228 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 228 275 (accept_3_2 43 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 228 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 228 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 228 275 (accept_3_2 40 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 228 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 228 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 228 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 228 275 (accept_3_2 37 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 228 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 228 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 228 275 (accept_3_2 34 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 228 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 228 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 228 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 228 275 (accept_3_2 31 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 228 275 (Polychromatic418967fa.accept_14_2_4_9_1_2121 30 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 228 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 228 275 (accept_3_2 28 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 228 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 228 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 228 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 228 275 (accept_3_2 25 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 228 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 228 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 228 275 (accept_3_2 22 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 228 275 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 228 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 228 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 228 275 (accept_3_2 19 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 228 275 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 228 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 275 (accept_3_2 16 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 228 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 228 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 228 275
  (Polychromatic418967fa.accept_20_14_8_15_1_8432 14 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 228 275 (accept_3_2 13 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 228 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 228 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 228 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 228 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 275 (accept_3_2 10 228 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 228 275 (Polychromatic418967fa.accept_13_9_7_2_1_3869
  9 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 228 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 228 275 (accept_3_2 7 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  228 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 228 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 228 275 (accept_3_2 4 228 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 228 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 228 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 228 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 228 275 (accept_3_2 1 228 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  275)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 227 275 (Eq.refl Bool.true) (allA_succ_of_accept 48
  227 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 227 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 227 275 (accept_3_2 46 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 227 275 (Polychromatic418967fa.accept_20_5_7_15_1_2668 45 227 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 227 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 227 275 (accept_3_2 43 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 227 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 227 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 227 275 (accept_3_2 40 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 227 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 227 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 227 275
  (Polychromatic418967fa.accept_10_8_7_5_1_602 38 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 227 275 (accept_3_2 37 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 227 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 227 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 227 275 (accept_3_2 34 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 227 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 227 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 227 275
  (Polychromatic418967fa.accept_10_2_7_5_1_605 32 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 227 275 (accept_3_2 31 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 227 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 227 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 227 275 (accept_3_2 28 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 227 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 227 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 227 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 227 275 (accept_3_2 25 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 227 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 227 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 227 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 227 275 (accept_3_2 22 227 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 227 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 227 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 227 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 227 275 (accept_3_2 19 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 227 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 227 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 275 (accept_3_2 16 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 227 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 275
  (Polychromatic418967fa.accept_13_1_6_2_1_377 14 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 227 275 (accept_3_2 13 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 227 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 227 275 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 227 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 275 (accept_3_2 10 227 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 275 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 227 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 227 275 (accept_3_2 7 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  227 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 227 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 275 (accept_3_2 4 227 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 227 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 275
  (Polychromatic418967fa.accept_10_2_7_5_1_605 2 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 275 (accept_3_2 1 227 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  275))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 226 275 (Eq.refl Bool.true) (allA_of_3_0 50 226
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 225 275 (Eq.refl Bool.true) (allA_succ_of_gcd 50 225 275
  25 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 225
  275 (accept_3_2 49 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 225 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 225 275 (Polychromatic418967fa.accept_17_13_4_3_1_1446 47 225 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 225 275 (accept_3_2 46 225 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 225 275 5 9 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 225 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 225 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 225 275 (accept_3_2 43 225 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 225 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 225 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 225 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 225 275 5 8 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 225 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 225 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 225 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 225 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 225 275 (accept_3_2 37 225 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 225 275 (Polychromatic418967fa.accept_14_8_1_9_1_2085
  36 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 225 275 5 7 45 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 225 275
  (accept_3_2 34 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 275
  (Polychromatic418967fa.accept_17_16_4_3_1_3429 33 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 225 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 225 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 225 275 (accept_3_2 31 225 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 225 275 5 6 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 225 275 (Polychromatic418967fa.accept_16_13_1_3_1_2205 29 225 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 275 (accept_3_2 28 225 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 225 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 225 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 225 275 25 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 225 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 225 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 275 (Polychromatic418967fa.accept_19_4_16_9_1_10315 23 225
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 275 (accept_3_2 22 225
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 275
  (Polychromatic418967fa.accept_20_1_5_15_1_6913 21 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 225 275 5 4 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 225 275 (accept_3_2 19 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 225 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 225 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 225 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 275 (accept_3_2 16 225 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 225 275 5 3 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 225 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 275 (accept_3_2 13 225 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 275
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 225 275 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 225 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 225 275 5 2 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 225 275 (Polychromatic418967fa.accept_20_9_5_15_1_3965
  9 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 275 (accept_3_2 7 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  225 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 225 275 5 1 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 225 275 (accept_3_2 4 225 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 225 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 225 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 225 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 275 (accept_3_2 1 225 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 275)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 224 275 (Eq.refl Bool.true) (allA_succ_of_accept 51 224 275 (Polychromatic418967fa.accept_6_3_2_5_1_32
  51 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 224 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 224 275 (accept_3_2 49 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 224 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 224 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 224 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 224 275 (accept_3_2 46 224 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 224 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 224 275
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 44 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 224 275 (accept_3_2 43 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 224 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 224 275 (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 224 275 (accept_3_2 40 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 224 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 224 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 224 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 224 275 (accept_3_2 37 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 224 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 224 275 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 224 275 (accept_3_2 34 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 224 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 224 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 224 275
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 224 275 (accept_3_2 31 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 224 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 224 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 224 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 224 275 (accept_3_2 28 224 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 224 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 224 275
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 224 275 (accept_3_2 25 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 224 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 224 275 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 224 275 (accept_3_2 22 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 224 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 224 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 224 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 224 275 (accept_3_2 19 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 224 275 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 224 275 (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 224 275 (accept_3_2 16 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 224 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 224 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 224 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 224 275 (accept_3_2 13 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 224 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 224 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 224 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 224 275 (accept_3_2 10 224 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 224 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 224 275
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 224 275 (accept_3_2 7 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  224 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 224 275 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 224 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 275 (accept_3_2 4 224 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 224 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 224 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 224 275 (accept_3_2 1 224 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  275)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 223 275 (Eq.refl Bool.true) (allA_of_3_0 53 223
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 222 275 (Eq.refl Bool.true) (allA_succ_of_accept 53 222
  275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 222 275 (accept_3_2 52 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 222 275 (Polychromatic418967fa.accept_13_12_1_2_1_845 51 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 222 275 (Polychromatic418967fa.accept_20_10_2_15_1_1517 50 222 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 222 275 (accept_3_2 49 222 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 222 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 222 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 222 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 222 275 (accept_3_2 46 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 222 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 222 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 222 275 (accept_3_2 43 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 222 275 (Polychromatic418967fa.accept_13_3_1_2_1_2960 42 222 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 222 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 222 275 (accept_3_2 40 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 222 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 222 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 222 275 (accept_3_2 37 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 222 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 222 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 222 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 222 275 (accept_3_2 34 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 222 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 222 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 222 275 (accept_3_2 31 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 222 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 222 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 222 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 222 275 (accept_3_2 28 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 222 275 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 222 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 222 275 (accept_3_2 25 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 222 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 222 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 222 275
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 222 275 (accept_3_2 22 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 222 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 222 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 222 275 (accept_3_2 19 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 222 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 222 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 222 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 222 275 (accept_3_2 16 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 222 275 (Polychromatic418967fa.accept_17_15_1_3_1_1488 15 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 222 275 (Polychromatic418967fa.accept_21_14_12_2_1_15508 14 222 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 275 (accept_3_2 13 222 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 222 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 222 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 222 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 222 275 (accept_3_2 10 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  222 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 222 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 275 (accept_3_2 7 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 275 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 222 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 222 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 222 275 (accept_3_2 4 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  222 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 222 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 222 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 275 (accept_3_2 1 222 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 222 275)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 221 275
  (Eq.refl Bool.true) (allA_succ_of_accept 54 221 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 221 275
  (Polychromatic418967fa.accept_15_8_11_5_1_169 53 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 221 275 (accept_3_2 52 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 221 275 (Polychromatic418967fa.accept_15_6_11_5_1_168 51 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 221 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 221 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 221 275 (accept_3_2 49 221 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 221 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 221 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 221 275 (accept_3_2 46 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 221 275 (Polychromatic418967fa.accept_20_5_1_15_1_3928 45 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 221 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 221 275 (accept_3_2 43 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 221 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 221 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 221 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 221 275 (accept_3_2 40 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 221 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 221 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 221 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 221 275 (accept_3_2 37 221 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 221 275 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 221 275
  (Polychromatic418967fa.accept_19_16_12_9_1_10223 35 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 221 275 (accept_3_2 34 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 221 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 221 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 275 (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 221
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 221 275 (accept_3_2 31 221
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 221 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 221 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 221 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 275 (accept_3_2 28 221 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 221 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 221 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 221 275 (accept_3_2 25
  221 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 221 275
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 221 275 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 221 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 275 (accept_3_2 22 221 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 221 275 (Polychromatic418967fa.accept_15_6_11_5_1_168 21 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 221 275 (accept_3_2 19 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 221 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 221 275 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 275 (accept_3_2 16 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 275 (Polychromatic418967fa.accept_16_15_13_3_1_4215 15 221
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 221 275 (accept_3_2 13 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 221 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 275 (Polychromatic418967fa.accept_23_11_14_22_1_15218 11 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 275 (accept_3_2 10 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 221 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 275
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 275 (accept_3_2 7 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 221 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 275 (accept_3_2 4 221 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 275 (Polychromatic418967fa.accept_19_3_12_9_1_3308 3 221 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 275 (accept_3_2 1 221 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 220 275 (Eq.refl Bool.true) (allA_of_3_0 56
  220 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 219 275 (Eq.refl Bool.true) (allA_succ_of_accept 56
  219 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 219 275 (accept_3_2 55 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 219 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 219 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 219 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 219 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 219 275 (accept_3_2 52 219 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 219 275 (Polychromatic418967fa.accept_9_6_3_5_1_240
  51 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 219 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 219 275 (accept_3_2 49 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 219 275 (Polychromatic418967fa.accept_13_9_11_2_1_1491 48 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 219 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 219 275 (accept_3_2 46 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 219 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 219 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 219 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 219 275 (accept_3_2 43 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 219 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 219 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 219 275 (accept_3_2 40 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 219 275 (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 219 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 219 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 219 275 (accept_3_2 37 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 219 275 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 219 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 219 275 (accept_3_2 34 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 219 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 219 275 (accept_3_2 31 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 219 275 (Polychromatic418967fa.accept_13_4_11_2_1_1458 30 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 219 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 275 (accept_3_2 28 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 219 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 219 275 (accept_3_2 25 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 219 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 219 275 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 219 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 275 (accept_3_2 22 219 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 219 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 275 (accept_3_2 19 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 219 275 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 219 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 275 (accept_3_2 16 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 219 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 275 (accept_3_2 13 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 219 275 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 275 (accept_3_2 10 219 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 219 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 275 (accept_3_2 7 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  219 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 219 275 (Polychromatic418967fa.accept_20_5_19_15_1_3946 5 219 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 275 (accept_3_2 4 219 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 275 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 219
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 275 (accept_3_2 1 219 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 218 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 218 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 218 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 218 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 218
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 218 275 (accept_3_2 55 218
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 218 275
  (Polychromatic418967fa.accept_23_8_11_22_1_7066 54 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 218 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 218 275 (accept_3_2 52 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 218 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 218 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 218 275
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 50 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 218 275 (accept_3_2 49 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 218 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 218 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 218 275 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 218
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 218 275 (accept_3_2 46 218
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 218 275 (Polychromatic418967fa.accept_4_1_2_3_1_9
  45 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 218 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 218 275 (accept_3_2 43 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 218 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 218 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 218 275 (accept_3_2 40 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 218 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 218 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 218 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 218 275 (accept_3_2 37 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 218 275 (Polychromatic418967fa.accept_17_2_14_3_1_4679 36 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 218 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 218 275 (accept_3_2 34 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 218 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 218 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 218 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 218 275 (accept_3_2 31 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 218 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 218 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 218 275 (accept_3_2 28 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 218 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 218 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 218 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 218 275 (accept_3_2 25 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 218 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 218 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 218 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 218 275 (accept_3_2 22 218 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 218 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 218 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 218 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 218 275 (accept_3_2 19 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 218 275 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 218 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 218 275 (accept_3_2 16 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 218 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 218 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 218 275
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 218 275 (accept_3_2 13 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 218 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 218 275 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 218 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 218 275 (accept_3_2 10 218 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 218 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 218 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 218 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 218 275 (accept_3_2 7 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  218 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 218 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 218 275 (accept_3_2 4 218 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 218 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 218 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 218 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 218 275 (accept_3_2 1 218 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 217 275 (Eq.refl Bool.true) (allA_of_3_0
  59 217 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 216 275 (Eq.refl Bool.true) (allA_succ_of_accept 59
  216 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 216 275 (accept_3_2 58 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 216 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 216 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 216 275 (Polychromatic418967fa.accept_15_11_6_5_1_1295 56 216
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 216 275 (accept_3_2 55 216
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 216 275
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 216 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 216 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 216 275 (accept_3_2 52 216 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 216 275 (Polychromatic418967fa.accept_10_1_6_5_1_304 51 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 216 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 216 275 (accept_3_2 49 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 216 275 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 216 275 (Polychromatic418967fa.accept_26_21_8_15_1_16939 47 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 216 275 (accept_3_2 46 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 216 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 216 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 216 275
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 216 275 (accept_3_2 43 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 216 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 216 275 (Polychromatic418967fa.accept_10_1_6_5_1_304 41 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 216 275 (accept_3_2 40 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 216 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 216 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 216 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 216 275 (accept_3_2 37 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 216 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 216 275 (Polychromatic418967fa.accept_19_16_7_9_1_7321 35 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 216 275 (accept_3_2 34 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 216 275 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 216
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 216 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 216 275 (accept_3_2 31 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 216 275 (Polychromatic418967fa.accept_19_11_7_9_1_8873 30 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 216 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 216 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 216 275 (accept_3_2 28 216 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 216 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 216 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 216 275
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 216 275 (accept_3_2 25 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 216 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 216 275 (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 275 (accept_3_2 22 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 216 275 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 216
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 216 275
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 216 275 (accept_3_2 19 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 216 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 216 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 216 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 216 275 (accept_3_2 16 216 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 216 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 275
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 216 275 (accept_3_2 13 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 216 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 216 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 216 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 216 275 (accept_3_2 10 216 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 216 275 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 216 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 216 275 (accept_3_2 7 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  216 275 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 216 275 (Polychromatic418967fa.accept_16_5_8_3_1_4240 5 216 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 275 (accept_3_2 4 216 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 216 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 216 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 275
  (Polychromatic418967fa.accept_19_2_7_9_1_1114 2 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 216 275 (accept_3_2 1 216 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 215 275 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 215 275 5 12 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 215 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 215 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 215 275 (accept_3_2 58 215 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 215 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 215 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 215 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 215 275 5 11 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 215 275 (Polychromatic418967fa.accept_19_16_6_9_1_7335 54 215 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 215 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 215 275 (accept_3_2 52 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 215 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 215 275 5 10 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 215 275 (accept_3_2 49 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 215 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 215 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 215 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 215 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 215 275 (accept_3_2 46 215 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 215 275 5 9 43 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 215 275
  (Polychromatic418967fa.accept_8_4_7_3_1_144 44 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 215 275 (accept_3_2 43 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 215 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 215 275 (Polychromatic418967fa.accept_16_9_7_3_1_614 41 215 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 215 275 5 8 43 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 215 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 215 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 215 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 275 (accept_3_2 37 215 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 215 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 215 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 215 275 5 7 43 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 215 275 (accept_3_2 34 215 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 215 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 215 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 215 275 (accept_3_2 31 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  215 275 5 6 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 215 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 215 275 (accept_3_2 28 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 215 275 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 215 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 215 275 (Polychromatic418967fa.accept_16_10_7_3_1_6601 26 215
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 215 275 5 5 43 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 215 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 215 275 (Polychromatic418967fa.accept_26_23_7_15_1_16938 23 215 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 275 (accept_3_2 22 215 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 215 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 215 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 215 275 5 4 43 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 215 275 (accept_3_2 19 215 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 275 (Polychromatic418967fa.accept_7_4_5_2_1_243
  18 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 275 (accept_3_2 16 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  215 275 5 3 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 215 275 (Polychromatic418967fa.accept_17_14_11_3_1_4653 14 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 215 275 (accept_3_2 13 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 215 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 215 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 215 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 215 275 5 2 43 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 215 275
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 215 275 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 215 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 275 (accept_3_2 7 215 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 215 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 215 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 215 275 5 1 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 215 275 (accept_3_2 4 215 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 215 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 275 (accept_3_2 1 215 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 214 275 (Eq.refl Bool.true)
  (allA_of_3_0 62 214 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 213 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 213 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 213 275 (accept_3_2 61 213 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 213 275 (Polychromatic418967fa.accept_18_6_15_5_1_6563 60 213 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 213 275
  (Polychromatic418967fa.accept_13_7_5_2_1_401 59 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 213 275 (accept_3_2 58 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 213 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 213 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 275 (accept_3_2 55 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 213 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 213 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 213 275 (accept_3_2 52 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 213 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 275 (accept_3_2 49 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 213 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 213 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 213 275 (accept_3_2 46 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 213 275 (Polychromatic418967fa.accept_17_11_9_3_1_1463 45 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 213 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 275 (accept_3_2 43 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 213 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 213 275 (accept_3_2 40 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 213 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 275 (accept_3_2 37 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 213 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 213 275 (accept_3_2 34 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 213 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 213 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 275 (accept_3_2 31 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 213 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 275 (accept_3_2 28 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 213 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 275 (accept_3_2 25 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 275 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 213 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 275
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 275 (accept_3_2 22 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 213 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 213 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 275 (accept_3_2 19 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 213 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 275 (accept_3_2 16 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 213 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 275 (accept_3_2 13 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 213 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 275 (accept_3_2 10 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 275 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 275 (accept_3_2 7 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 213 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 275 (accept_3_2 4 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 213 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 275 (accept_3_2 1 213 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  212 275 (Eq.refl Bool.true) (allA_succ_of_accept 63 212 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 212 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 212 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 212 275 (accept_3_2 61 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 212 275 (Polychromatic418967fa.accept_14_4_2_9_1_2092 60 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 212 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 59 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 212 275 (accept_3_2 58 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 212 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 212 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 212 275
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 56 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 212 275 (accept_3_2 55 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 212 275 (Polychromatic418967fa.accept_16_6_4_3_1_2189 54 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 212 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 212 275 (accept_3_2 52 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 212 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 212 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 212 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 212 275 (accept_3_2 49 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 212 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 212 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 212 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 212 275 (accept_3_2 46 212 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 212 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 212 275
  (Polychromatic418967fa.accept_13_5_4_2_1_846 44 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 212 275 (accept_3_2 43 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 212 275 (Polychromatic418967fa.accept_15_12_2_5_1_3939 42 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 212 275 (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 212 275 (accept_3_2 40 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 212 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 212 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 212 275
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 212 275 (accept_3_2 37 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 212 275 (Polychromatic418967fa.accept_24_12_20_11_1_15144 36 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 212 275 (Polychromatic418967fa.accept_14_7_2_9_1_2093 35 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 212 275 (accept_3_2 34 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 212 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 212 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 212 275
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 32 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 212 275 (accept_3_2 31 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 212 275 (Polychromatic418967fa.accept_17_13_8_3_1_7177 30 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 212 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 212 275 (accept_3_2 28 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 212 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 212 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 212 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 212 275 (accept_3_2 25 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 212 275 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 212 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 212 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 212 275 (accept_3_2 22 212 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 212 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 212 275
  (Polychromatic418967fa.accept_22_20_14_11_1_12258 20 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 212 275 (accept_3_2 19 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 212 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 212 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 212 275 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 212
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 212 275 (accept_3_2 16 212
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 212 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 212 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 212 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 212 275 (accept_3_2 13 212 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 212 275 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 212 275
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 212 275 (accept_3_2 10 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  212 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 212 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 212 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 275 (accept_3_2 7 212 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 212 275 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 212 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 212 275
  (Polychromatic418967fa.accept_13_5_4_2_1_846 5 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 212 275 (accept_3_2 4 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  212 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 212 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 212 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 275 (accept_3_2 1 212 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65
  211 275 (Eq.refl Bool.true) (allA_of_3_0 65 211 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 210 275
  (Eq.refl Bool.true) (allA_succ_of_gcd 65 210 275 5 13 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 210 275 (accept_3_2 64 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 210 275 (Polychromatic418967fa.accept_16_15_2_3_1_4262 63 210 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 210 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 210 275 (accept_3_2 61 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  210 275 5 12 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 210 275 (Polychromatic418967fa.accept_19_2_1_9_1_10240 59 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 210 275 (accept_3_2 58 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 210 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 210 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 210 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 56
  210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 210 275 5 11 42 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 210 275
  (Polychromatic418967fa.accept_16_6_2_3_1_4223 54 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 210 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 210 275 (accept_3_2 52 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 210 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 210 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 210 275 5 10 42 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 210 275 (accept_3_2 49 210 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 210 275 (Polychromatic418967fa.accept_17_14_6_3_1_2362 48 210
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 210 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 210 275 (accept_3_2 46 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  210 275 5 9 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 210 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 210 275 (accept_3_2 43 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 210 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 210 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 210 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 210 275 5 8 42 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 210 275
  (Polychromatic418967fa.accept_17_5_6_3_1_4640 39 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 210 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 210 275 (accept_3_2 37 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 210 275 (Polychromatic418967fa.accept_19_17_1_9_1_4595 36 210 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 210 275 5 7 42 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 210 275 (accept_3_2 34 210 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 210 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 210 275
  (Polychromatic418967fa.accept_20_12_10_15_1_9869 32 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 210 275 (accept_3_2 31 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 275 5 6 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 210 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 210 275 (accept_3_2 28 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 210 275 (Polychromatic418967fa.accept_18_9_12_5_1_864 27 210 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 210 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 210 275 5 5 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 210 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 210 275 (Polychromatic418967fa.accept_20_3_10_15_1_620 23 210
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 210 275 (accept_3_2 22 210
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 210 275 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 210 275 5 4 42 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 275
  (accept_3_2 19 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 210 275
  (Polychromatic418967fa.accept_17_1_6_3_1_4700 18 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 210 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 275 (accept_3_2 16 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 210 275 5 3 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 210 275 (Polychromatic418967fa.accept_17_14_6_3_1_2362 14 210 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 210 275 (accept_3_2 13 210 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 210 275 (Polychromatic418967fa.accept_19_12_1_9_1_10281 12 210
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 210 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 210 275 5 2 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 210 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 210 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 275 (accept_3_2 7 210 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 210 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 6
  210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 210 275 5 1 42 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 210 275 (accept_3_2 4
  210 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 275
  (Polychromatic418967fa.accept_20_3_10_15_1_620 3 210 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 210 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 275 (accept_3_2 1 210 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 210 275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 209 275
  (Eq.refl Bool.true) (allA_succ_of_gcd 66 209 275 11 6 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 209 275 (Polychromatic418967fa.accept_20_5_9_15_1_3973 65 209
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 209 275 (accept_3_2 64 209
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 209 275
  (Polychromatic418967fa.accept_20_3_9_15_1_6847 63 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 209 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 209 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 209 275 (accept_3_2 61 209 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 209 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 209 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 59
  209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 209 275 (accept_3_2 58
  209 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 209 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 209 275 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 209 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 209 275 11 5 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 209 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 209 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 209 275 (accept_3_2 52 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 209 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 209 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 209 275 (accept_3_2 49 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 209 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 209 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 209 275
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 209 275 (accept_3_2 46 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 209 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 209 275 11 4 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 209 275 (accept_3_2 43 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 209 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 209 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 209 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 209 275 (accept_3_2 40 209 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 209 275 (Polychromatic418967fa.accept_7_4_6_2_1_451
  39 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 209 275 (accept_3_2 37 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 209 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 209 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 209 275 (accept_3_2 34 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 33 209 275 11 3 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 209 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 209 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 275 (accept_3_2 31 209 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 209 275 (accept_3_2 28 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 209 275 (Polychromatic418967fa.accept_21_6_20_2_1_16937 27 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 209 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 275 (accept_3_2 25 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 209 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 275
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 209 275 11 2 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 209 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 275 (Polychromatic418967fa.accept_16_4_1_3_1_6581
  20 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 275 (accept_3_2 19
  209 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 209 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 209 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 275 (accept_3_2 16 209 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 209 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 275 (accept_3_2 13
  209 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 275
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 209 275 11 1 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 209 275 (accept_3_2 10 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 209 275 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 209 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 209 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 275 (accept_3_2 7 209 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 275
  (Polychromatic418967fa.accept_20_5_9_15_1_3973 5 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 275 (accept_3_2 4 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 209 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 275 (accept_3_2 1 209 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 208 275 (Eq.refl Bool.true) (allA_of_3_0 68 208 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 207 275
  (Eq.refl Bool.true) (allA_succ_of_accept 68 207 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 207 275 (accept_3_2 67 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 207 275 (Polychromatic418967fa.accept_13_1_12_2_1_384 66 207
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 207 275
  (Polychromatic418967fa.accept_19_8_17_9_1_4542 65 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 207 275 (accept_3_2 64 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 207 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 207 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 207 275 (accept_3_2 61 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 207 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 207 275
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 59 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 207 275 (accept_3_2 58 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 207 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 207 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 207 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 207 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 275 (accept_3_2 55 207 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 207 275 (Polychromatic418967fa.accept_7_5_4_2_1_235
  54 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 207 275
  (Polychromatic418967fa.accept_10_3_7_5_1_288 53 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 207 275 (accept_3_2 52 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 207 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 51 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 207 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 275 (accept_3_2 49 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 207 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 275 (accept_3_2 46 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 207 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 207 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 275 (accept_3_2 43 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 207 275 (accept_3_2 40 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 207 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 207 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 275 (accept_3_2 37 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 275
  (Polychromatic418967fa.accept_22_13_9_11_1_13815 35 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 207 275 (accept_3_2 34 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 207 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 207 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 207 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 275 (accept_3_2 31 207 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 275
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 30 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 207 275 (Polychromatic418967fa.accept_13_3_12_2_1_385 29 207 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 275 (accept_3_2 28 207 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 207 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 26
  207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 275 (accept_3_2 25
  207 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 275
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 207 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 207 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 275 (accept_3_2 22 207 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 207 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 275 (accept_3_2 19 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 207 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 207 275 (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 275 (accept_3_2 16 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 275 (Polychromatic418967fa.accept_18_15_9_5_1_3934 15 207
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 275 (accept_3_2 13 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 207 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 207 275 (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 275 (accept_3_2 10 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 207
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 275 (accept_3_2 7 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  207 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 207 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 275 (accept_3_2 4 207 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 207 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 275 (accept_3_2 1 207 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 206 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 206 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 206 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 206 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 206 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 206 275 (accept_3_2 67 206 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 206 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 66
  206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 206 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 206 275 (accept_3_2 64 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 206 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 206 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 206 275 (accept_3_2 61 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 206 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 206 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 206 275
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 206 275 (accept_3_2 58 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 206 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 206 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 206 275 (accept_3_2 55 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 206 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 206 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 206 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 206 275 (accept_3_2 52 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 206 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 206 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 206 275 (accept_3_2 49 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 206 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 206 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 206 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 206 275 (accept_3_2 46 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 206 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 206 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 44 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 206 275 (accept_3_2 43 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 206 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 206 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 206 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 206 275 (accept_3_2 40 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 206 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 206 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 206 275 (accept_3_2 37 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 206 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 206 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 206 275
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 206 275 (accept_3_2 34 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 206 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 206 275 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 206 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 206 275 (accept_3_2 31 206 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 206 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 206 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 206 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 206 275 (accept_3_2 28 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 206 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 206 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 206 275 (accept_3_2 25 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 206 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 206 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 206 275
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 206 275 (accept_3_2 22 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 206 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 206 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 206 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 206 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 206 275 (accept_3_2 19 206 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 206 275 (Polychromatic418967fa.accept_17_1_2_3_1_4668
  18 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 206 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 206 275 (accept_3_2 16 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 206 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 206 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 206 275 (accept_3_2 13 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 206 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 206 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 206 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 206 275 (accept_3_2 10 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  206 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 206 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 206 275 (accept_3_2 7 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 206 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 206 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 206 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 206 275 (accept_3_2 4 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  206 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 206 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 206 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 206 275 (accept_3_2 1 206 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 206 275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 205 275 (Eq.refl Bool.true) (allA_of_3_0 71 205 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 72 204 275 (Eq.refl Bool.true) (allA_succ_of_accept 71 204 275 (Polychromatic418967fa.accept_8_7_4_3_1_156
  71 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 204 275 (accept_3_2 70
  204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 204 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 204 275 (Polychromatic418967fa.accept_13_3_9_2_1_1486 68 204 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 204 275 (accept_3_2 67 204 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 204 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 204 275 (Polychromatic418967fa.accept_9_2_6_5_1_227
  65 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 204 275 (accept_3_2 64
  204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 204 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 63 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 204 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 204 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 204 275 (accept_3_2 61 204 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 204 275 (Polychromatic418967fa.accept_19_3_14_9_1_8866 60 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 204 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 204 275 (accept_3_2 58 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 204 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 204 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 204 275 (accept_3_2 55 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 204 275 (Polychromatic418967fa.accept_19_16_14_9_1_7316 54 204 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 204 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 204 275 (accept_3_2 52 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 204 275 (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 204 275 (Polychromatic418967fa.accept_13_11_9_2_1_2969 50 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 204 275 (accept_3_2 49 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 204 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 204 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 204 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 204 275 (accept_3_2 46 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 204 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 204 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 204 275 (accept_3_2 43 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 204 275 (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 204 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 204 275 (accept_3_2 40 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 204 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 204 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 204 275 (accept_3_2 37 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 204 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 204 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 204 275 (accept_3_2 34 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 204 275 (Polychromatic418967fa.accept_13_7_9_2_1_2167 33 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 204 275 (Polychromatic418967fa.accept_13_6_9_2_1_838 32 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 204 275 (accept_3_2 31 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 204 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 204 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 204 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 204 275 (accept_3_2 28 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 204 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 204 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 275 (accept_3_2 25 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 204 275
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 204 275 (accept_3_2 22 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 204 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 204 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 275 (accept_3_2 19 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 275 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 204 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 204 275 (accept_3_2 16 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 204 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 204 275 (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 275 (accept_3_2 13 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 204 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 204 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 204 275 (accept_3_2 10 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  204 275 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 204 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 275 (accept_3_2 7 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 204 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 204 275
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 204 275 (accept_3_2 4 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  204 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 204 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 204 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 275 (accept_3_2 1 204 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 204 275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 73 203 275 (Eq.refl Bool.true) (allA_succ_of_accept 72 203 275
  (Polychromatic418967fa.accept_10_2_3_5_1_996 72 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 203 275 (Polychromatic418967fa.accept_13_6_8_2_1_1484 71 203 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 203 275 (accept_3_2 70 203 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 203 275 (Polychromatic418967fa.accept_20_9_3_15_1_3929 69 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 203 275
  (Polychromatic418967fa.accept_10_8_3_5_1_613 68 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 203 275 (accept_3_2 67 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 203 275 (Polychromatic418967fa.accept_21_3_14_2_1_7978 66 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 203 275 (Polychromatic418967fa.accept_20_5_3_15_1_6909 65 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 203 275 (accept_3_2 64 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 203 275 (Polychromatic418967fa.accept_15_3_8_5_1_2105 63 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 203 275
  (Polychromatic418967fa.accept_10_2_3_5_1_996 62 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 203 275 (accept_3_2 61 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 203 275 (Polychromatic418967fa.accept_19_3_13_9_1_8876 60 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 203 275 (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 203 275 (accept_3_2 58 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 203 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 203 275
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 203 275 (accept_3_2 55 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 203 275 (Polychromatic418967fa.accept_14_12_7_9_1_726 54 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 203 275 (Polychromatic418967fa.accept_19_15_13_9_1_7324 53 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 203 275 (accept_3_2 52 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 203 275 (Polychromatic418967fa.accept_21_9_14_2_1_6370 51 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 203 275
  (Polychromatic418967fa.accept_20_10_3_15_1_1546 50 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 203 275 (accept_3_2 49 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 203 275 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 203 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 203 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 203 275 (accept_3_2 46 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 203 275
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 203 275 (Polychromatic418967fa.accept_14_2_7_9_1_2937 44 203 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 203 275 (accept_3_2 43 203 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 203 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 203 275
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 203 275 (accept_3_2 40 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 203 275 (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 203 275 (Polychromatic418967fa.accept_10_8_3_5_1_613 38 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 275 (accept_3_2 37 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 203 275 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 275
  (Polychromatic418967fa.accept_22_13_5_11_1_15478 35 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 203 275 (accept_3_2 34 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 203 275 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 203 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 203 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 275 (accept_3_2 31 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 275
  (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 203 275 (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 203 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 203 275 (accept_3_2 28 203 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 203 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 275
  (Polychromatic418967fa.accept_14_12_7_9_1_726 26 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 203 275 (accept_3_2 25 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 203 275 (Polychromatic418967fa.accept_16_8_11_3_1_4279 24 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 203 275 (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 275 (accept_3_2 22 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 275 (Polychromatic418967fa.accept_17_4_16_3_1_4620 21 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 275
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 203 275 (accept_3_2 19 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 203 275 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 203 275 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 275 (accept_3_2 16 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 203 275 (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 275
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 203 275 (accept_3_2 13 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 203 275 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 203 275 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 275 (accept_3_2 10 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 275 (Polychromatic418967fa.accept_20_9_3_15_1_3929 9 203
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 275
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 203 275 (accept_3_2 7 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  203 275 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 203 275 (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 203 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 275 (accept_3_2 4 203 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 275 (Polychromatic418967fa.accept_15_3_8_5_1_2105 3 203 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 275
  (Polychromatic418967fa.accept_10_2_3_5_1_996 2 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 275 (accept_3_2 1 203 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 202 275 (Eq.refl
  Bool.true) (allA_of_3_0 74 202 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 201 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 74 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 201 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 201 275 (accept_3_2 73 201 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 201 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 72 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 201 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 201 275 (accept_3_2 70 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 201 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 201 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 201 275 (accept_3_2 67 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 201 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 201 275 (accept_3_2 64 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 201 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 201 275 (accept_3_2 61 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 201 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 201 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 201 275 (accept_3_2 58 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 201 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 57 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 201 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 275 (accept_3_2 55 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 201 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 201 275 (accept_3_2 52 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 201 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 275 (accept_3_2 49 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 201 275 (Polychromatic418967fa.accept_13_9_6_2_1_2200 48 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 201 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 201 275 (accept_3_2 46 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 201 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 201 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 275 (accept_3_2 43 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 201 275
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 201 275 (accept_3_2 40 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 201 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 275 (accept_3_2 37 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 201 275 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 201 275 (accept_3_2 34 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 201 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 201 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 275 (accept_3_2 31 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 201 275 (accept_3_2 28 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 201 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 275 (accept_3_2 25 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 275
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 201 275 (accept_3_2 22 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 201 275 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 201 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 275 (accept_3_2 19 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 201 275 (accept_3_2 16 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 201 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 275 (accept_3_2 13 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 275 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 201 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 275 (accept_3_2 10 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  201 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 201 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 275 (accept_3_2 7 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 201 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 275
  (Polychromatic418967fa.accept_20_5_1_15_1_3928 5 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 275 (accept_3_2 4 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 201 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 275 (accept_3_2 1 201 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 76 200 275 (Eq.refl Bool.true) (allA_succ_of_gcd 75 200 275 25 3 8 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 200 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 200 275 (accept_3_2 73 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 200 275 (Polychromatic418967fa.accept_13_7_5_2_1_401 72 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 200 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 200 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 200 275 5 14 40 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 200 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 69 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 200 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 200 275 (accept_3_2 67 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 200 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 200 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 200 275 5 13 40 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 200 275 (accept_3_2 64 200 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 200 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 200 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 200 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 200 275 (accept_3_2 61 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  200 275 5 12 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 200 275 (Polychromatic418967fa.accept_13_7_5_2_1_401 59 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 200 275 (accept_3_2 58 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 200 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 200 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 200 275 (Polychromatic418967fa.accept_13_4_5_2_1_1436
  56 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 200 275 5 11 40 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 200 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 200 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 200 275 (accept_3_2 52 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 200 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 200 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 200 275 25 2 8 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 200 275 (accept_3_2 49 200 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 200 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 200 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 200 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 200 275 (accept_3_2 46 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  200 275 5 9 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 200 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 200 275 (accept_3_2 43 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 200 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 200 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 200 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 200 275 5 8 40 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 200 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 200 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 200 275 (accept_3_2 37 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 200 275 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 200 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 200 275 5 7 40 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 200 275 (accept_3_2 34 200 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 200 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 200 275
  (Polychromatic418967fa.accept_19_13_10_9_1_5995 32 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 200 275 (accept_3_2 31 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 200 275 5 6 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 200 275 (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 200 275 (accept_3_2 28 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 200 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 200 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 275 (Polychromatic418967fa.accept_7_5_4_2_1_235
  26 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 200 275 25 1 8 11
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 200 275
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 200 275 (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 275 (accept_3_2 22 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 200 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 200 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 200 275 5 4 40 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 200 275 (accept_3_2 19 200 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 200 275 (Polychromatic418967fa.accept_19_18_10_9_1_5996 18 200
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 200 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 200 275 (accept_3_2 16 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  200 275 5 3 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 200 275 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 200 275 (accept_3_2 13 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 200 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 200 275 (Polychromatic418967fa.accept_16_11_8_3_1_3183 11 200
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 275 5 2 40 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 275
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 200 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 200 275 (accept_3_2 7 200 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 200 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 200 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 200 275 5 1 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 200 275 (accept_3_2 4 200 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 275 (accept_3_2 1 200 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 199 275 (Eq.refl
  Bool.true) (allA_of_3_0 77 199 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 198 275 (Eq.refl Bool.true)
  (allA_succ_of_gcd 77 198 275 11 7 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 198 275 (accept_3_2 76 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 198 275 (Polychromatic418967fa.accept_13_10_3_2_1_4728 75 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 198 275 (Polychromatic418967fa.accept_13_9_3_2_1_399 74 198
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 198 275 (accept_3_2 73 198
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 198 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 72 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 198 275 (Polychromatic418967fa.accept_19_14_8_9_1_4547 71 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 198 275 (accept_3_2 70 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 198 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 198 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 198 275 (Polychromatic418967fa.accept_15_8_3_5_1_608
  68 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 198 275 (accept_3_2 67
  198 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 198 275 11 6 18 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 198 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 198 275 (accept_3_2 64 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 198 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 198 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 62 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 198 275 (accept_3_2 61 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 198 275 (Polychromatic418967fa.accept_14_4_2_9_1_2092 60 198
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 198 275
  (Polychromatic418967fa.accept_16_11_6_3_1_6564 59 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 198 275 (accept_3_2 58 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 198 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 198 275 (Polychromatic418967fa.accept_19_18_8_9_1_3325 56 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 198 275 11 5 18 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 198 275
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 54 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 198 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 198 275 (accept_3_2 52 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 198 275 (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 198 275
  (Polychromatic418967fa.accept_13_11_3_2_1_863 50 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 198 275 (accept_3_2 49 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 198 275 (Polychromatic418967fa.accept_13_9_3_2_1_399 48 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 198 275 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 198 275 (accept_3_2 46 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 198 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 198 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 198 275 11 4 18 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 198 275 (accept_3_2 43
  198 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 198 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 198 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 198 275 (accept_3_2 40 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 198 275 (Polychromatic418967fa.accept_14_11_2_9_1_5873 39 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 198 275
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 38 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 198 275 (accept_3_2 37 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 198 275 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 198 275 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 198 275 (accept_3_2 34 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 198 275 11 3 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 198 275 (Polychromatic418967fa.accept_10_2_8_5_1_587
  32 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 275 (accept_3_2 31
  198 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 198 275
  (Polychromatic418967fa.accept_19_11_8_9_1_5993 30 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 198 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 198 275 (accept_3_2 28 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 198 275 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 275
  (Polychromatic418967fa.accept_17_9_11_3_1_2353 26 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 198 275 (accept_3_2 25 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 198 275 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 198 275 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 275 11 2 18 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 198 275 (Polychromatic418967fa.accept_16_4_6_3_1_1311 20 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 275 (accept_3_2 19 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 198 275 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 198 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 198 275 (accept_3_2 16 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 198 275 (Polychromatic418967fa.accept_21_15_9_2_1_7973 15 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 198 275 (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 275 (accept_3_2 13 198 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 198
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 198 275 11 1 18 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 198 275 (accept_3_2 10
  198 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 275
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 198 275 (Polychromatic418967fa.accept_15_8_3_5_1_608 8 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 275 (accept_3_2 7 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 198 275 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 198 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 198 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 198 275 (accept_3_2 4 198
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 198 275
  (Polychromatic418967fa.accept_10_3_8_5_1_606 3 198 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 198 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 275 (accept_3_2 1 198 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 198 275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 197 275 (Eq.refl Bool.true) (allA_succ_of_accept 78 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27
  78 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 197 275
  (Polychromatic418967fa.accept_17_9_10_3_1_3423 77 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 197 275 (accept_3_2 76 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 197 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 75 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 197 275 (accept_3_2 73 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 197 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 197 275
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 71 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 197 275 (accept_3_2 70 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 197 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 197 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 68 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 197 275 (accept_3_2 67 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 197 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 197 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 197 275 (accept_3_2 64 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 197 275 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 197 275 (accept_3_2 61 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 197 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 197 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 197 275 (accept_3_2 58 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 197 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 197 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 197 275 (accept_3_2 55 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 197 275
  (Polychromatic418967fa.accept_10_3_7_5_1_288 53 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 197 275 (accept_3_2 52 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 197 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 197 275 (accept_3_2 49 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 197 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 197 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 197 275 (accept_3_2 46 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 197 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 197 275 (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 197 275 (accept_3_2 43 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 197 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 197 275
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 197 275 (accept_3_2 40 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 197 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 197 275 (accept_3_2 37 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 197 275 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 197 275
  (Polychromatic418967fa.accept_19_16_7_9_1_7321 35 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 197 275 (accept_3_2 34 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 197 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 197 275 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 197 275 (accept_3_2 31 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 197 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 197 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 197 275 (accept_3_2 28 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 197 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 275 (accept_3_2 25 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 197 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 275
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 197 275 (accept_3_2 22 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 197 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 197 275 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 275 (accept_3_2 19 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 275
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 197 275 (accept_3_2 16 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 197 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 275 (accept_3_2 13 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 275 (accept_3_2 10 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 275 (Polychromatic418967fa.accept_17_9_10_3_1_3423 9 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 275 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 275 (accept_3_2 7 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 197 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 275
  (Polychromatic418967fa.accept_19_5_7_9_1_5954 5 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 275 (accept_3_2 4 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 275 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 197 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 275 (accept_3_2 1 197 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 196 275 (Eq.refl Bool.true) (allA_of_3_0 80 196 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 81 195 275 (Eq.refl Bool.true) (allA_succ_of_gcd 80 195 275 5 16 39 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 195 275 (accept_3_2 79 195 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 195 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 195 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 195 275
  (Polychromatic418967fa.accept_19_1_5_9_1_10341 77 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 195 275 (accept_3_2 76 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  195 275 5 15 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 195 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 195 275 (accept_3_2 73 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 195 275 (Polychromatic418967fa.accept_19_15_5_9_1_3299 72 195 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 195 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 195 275 5 14 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 195 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 195 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 195 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 195 275 (accept_3_2 67 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 195 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 195 275 5 13 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 195 275 (accept_3_2 64 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 195 275 (Polychromatic418967fa.accept_17_12_8_3_1_4646 63 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 195 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 195 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 195 275 (accept_3_2 61 195 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 195 275 5 12 39 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 195 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 195 275 (accept_3_2 58 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 195 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 195 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 195 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 195 275 5 11 39 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 195 275
  (Polychromatic418967fa.accept_21_12_6_2_1_7950 54 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 195 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 275 (accept_3_2 52 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 195 275 (Polychromatic418967fa.accept_19_13_5_9_1_3318 51 195 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 195 275 5 10 39 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 195 275 (accept_3_2 49 195 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 48
  195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 195 275 (accept_3_2 46 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  195 275 5 9 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 195 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 195 275 (accept_3_2 43 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 195 275 (Polychromatic418967fa.accept_18_6_15_5_1_6563 42 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 275 (Polychromatic418967fa.accept_21_20_6_2_1_11048 41 195
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 195 275 5 8 39 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 195 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 195 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 275 (accept_3_2 37 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 195 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 195 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 195 275 5 7 39 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 195 275 (accept_3_2 34 195 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 275 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 195
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 195 275 (accept_3_2 31 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  195 275 5 6 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 195 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 195 275 (accept_3_2 28 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 195 275 (Polychromatic418967fa.accept_18_9_15_5_1_6551 27 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 195 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 195 275 5 5 39 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 195 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 195 275 (Polychromatic418967fa.accept_19_4_5_9_1_8855 23 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 275 (accept_3_2 22 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 195 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 195 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 195 275 5 4 39 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 195 275 (accept_3_2 19 195 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 195 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 275 (accept_3_2 16 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  195 275 5 3 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 195 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 195 275 (accept_3_2 13 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 195 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 195 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 195 275 5 2 39 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 195 275
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 275 (accept_3_2 7 195 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 275 (Polychromatic418967fa.accept_18_6_15_5_1_6563 6 195 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 195 275 5 1 39 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 195 275 (accept_3_2 4 195 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 195 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 275
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 275 (accept_3_2 1 195 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 194 275 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 194 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 80
  194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 194 275 (accept_3_2 79
  194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 194 275
  (Polychromatic418967fa.accept_17_10_7_3_1_727 78 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 194 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 194 275 (accept_3_2 76 194 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 194 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 194 275 (Polychromatic418967fa.accept_7_4_5_2_1_243
  74 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 194 275 (accept_3_2 73
  194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 194 275
  (Polychromatic418967fa.accept_17_4_7_3_1_1417 72 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 194 275 (Polychromatic418967fa.accept_10_1_4_5_1_1031 71 194 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 194 275 (accept_3_2 70 194 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 194 275 (Polychromatic418967fa.accept_12_8_2_11_1_246
  68 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 194 275 (accept_3_2 67
  194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 194 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 194 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 194 275 (accept_3_2 64 194 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 194 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 194 275
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 62 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 194 275 (accept_3_2 61 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 194 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 194 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 194 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 194 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 194 275 (accept_3_2 58 194 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 194 275
  (Polychromatic418967fa.accept_10_6_4_5_1_615 56 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 194 275 (accept_3_2 55 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 194 275 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 194 275 (accept_3_2 52 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 194 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 194 275
  (Polychromatic418967fa.accept_17_16_7_3_1_4644 50 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 194 275 (accept_3_2 49 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 194 275 (Polychromatic418967fa.accept_19_10_4_9_1_7333 48 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 194 275 (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 194 275 (accept_3_2 46 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 194 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 194 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 194 275 (accept_3_2 43 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 194 275 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 194 275 (accept_3_2 40 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 194 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 194 275
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 194 275 (accept_3_2 37 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 194 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 194 275 (Polychromatic418967fa.accept_14_7_12_9_1_2926 35 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 194 275 (accept_3_2 34 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 194 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 194 275
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 194 275 (accept_3_2 31 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 194 275 (Polychromatic418967fa.accept_13_4_12_2_1_1459 30 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 275 (accept_3_2 28 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 194 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 194 275
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 194 275 (accept_3_2 25 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 194 275 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 194 275 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 194 275 (accept_3_2 22 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 194 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 194 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 194 275 (accept_3_2 19 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 194 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 194 275 (accept_3_2 16 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 194 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 194 275
  (Polychromatic418967fa.accept_13_1_12_2_1_384 14 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 194 275 (accept_3_2 13 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 194 275 (Polychromatic418967fa.accept_17_12_7_3_1_1498 12 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 194 275 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 275 (accept_3_2 10 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 275
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 275 (accept_3_2 7 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 275 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 275 (accept_3_2 4 194 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 194 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 275
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 275 (accept_3_2 1 194 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 193 275 (Eq.refl
  Bool.true) (allA_of_3_0 83 193 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 192 275 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 192 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 192 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 192 275 (accept_3_2 82 192 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 192 275 (Polychromatic418967fa.accept_13_3_10_2_1_381 81 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 192 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 80 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 192 275 (accept_3_2 79 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 192 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 192 275 (Polychromatic418967fa.accept_10_7_2_5_1_298 77 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 192 275 (accept_3_2 76 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 192 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 192 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 192 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 192 275 (accept_3_2 73 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 192 275 (Polychromatic418967fa.accept_19_15_2_9_1_10357 72 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 192 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 192 275 (accept_3_2 70 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 192 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 192 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 192 275 (accept_3_2 67 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 192 275 (Polychromatic418967fa.accept_15_6_12_5_1_2108 66 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 192 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 192 275 (accept_3_2 64 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 192 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 192 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 192 275 (accept_3_2 61 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 192 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 192 275 (Polychromatic418967fa.accept_17_8_5_3_1_2397 59 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 192 275 (accept_3_2 58 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 192 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 192 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 192 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 192 275 (accept_3_2 55 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 192 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 192 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 192 275 (accept_3_2 52 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 192 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 192 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 192 275 (accept_3_2 49 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 192 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 192 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 192 275 (accept_3_2 46 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 192 275 (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 192 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 192 275
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 192 275 (accept_3_2 43 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 192 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 192 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 275 (accept_3_2 40 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 192 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 192 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 192 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 192 275 (accept_3_2 37 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 192 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 192 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 275 (accept_3_2 34 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 192 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 192 275
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 32 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 192 275 (accept_3_2 31 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 192 275 (Polychromatic418967fa.accept_19_11_2_9_1_8897 30 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 192 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 275 (accept_3_2 28 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 192 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 192 275
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 192 275 (accept_3_2 25 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 192 275 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 192 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 275 (accept_3_2 22 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 192 275 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 192
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 192 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 192 275 (accept_3_2 19 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 192 275 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 192 275 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 275 (accept_3_2 16 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 192 275
  (Polychromatic418967fa.accept_21_14_3_2_1_12567 14 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 192 275 (accept_3_2 13 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 192 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 192 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 275 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 192 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 275 (accept_3_2 10 192 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 275 (Polychromatic418967fa.accept_15_9_12_5_1_1267
  9 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 192 275
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 192 275 (accept_3_2 7 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  192 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 192 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 275 (accept_3_2 4 192 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 275 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 192 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 275
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 192 275 (accept_3_2 1 192 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 191 275
  (Eq.refl Bool.true) (allA_succ_of_accept 84 191 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 191 275
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 83 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 191 275 (accept_3_2 82 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 191 275 (Polychromatic418967fa.accept_13_3_9_2_1_1486 81 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 191 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 191 275 (accept_3_2 79 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 191 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 191 275
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 77 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 191 275 (accept_3_2 76 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 191 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 191 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018 74 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 191 275 (accept_3_2 73 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 191 275 (Polychromatic418967fa.accept_13_7_9_2_1_2167 72 191
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 191 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 191 275 (accept_3_2 70 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 191 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 191 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 68 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 191 275 (accept_3_2 67 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 191 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 191 275
  (Polychromatic418967fa.accept_19_8_1_9_1_7329 65 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 191 275 (accept_3_2 64 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 191 275 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 191 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 191 275 (accept_3_2 61 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 191 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 191 275
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 191 275 (accept_3_2 58 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 191 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 191 275 (Polychromatic418967fa.accept_10_6_1_5_1_1024 56 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 191 275 (accept_3_2 55 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 191 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 191
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 191 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 191 275 (accept_3_2 52 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 191 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 191 275 (Polychromatic418967fa.accept_13_11_9_2_1_2969 50 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 191 275 (accept_3_2 49 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 191 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 191 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 191 275
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 191 275 (accept_3_2 46 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 191 275 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 191 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 191 275 (accept_3_2 43 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 191 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 275
  (Polychromatic418967fa.accept_17_7_4_3_1_3456 41 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 191 275 (accept_3_2 40 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 191 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 191 275 (Polychromatic418967fa.accept_15_8_11_5_1_169 38 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 275 (accept_3_2 37 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 191 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 275 (accept_3_2 34 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 275 (Polychromatic418967fa.accept_13_6_9_2_1_838 32 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 275 (accept_3_2 31 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 191 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 275
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 275 (accept_3_2 28 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 275 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 275 (accept_3_2 25 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 275
  (Polychromatic418967fa.accept_15_8_11_5_1_169 23 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 275 (accept_3_2 22 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 275 (accept_3_2 19 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 275 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 275
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 275 (accept_3_2 16 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 275 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 275 (accept_3_2 13 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 275 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 191 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 275
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 275 (accept_3_2 10 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 275 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 275 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 275 (accept_3_2 7 191 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 275 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 275
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 275 (accept_3_2 4 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 275 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 191 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 275 (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 275 (accept_3_2 1 191 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 191
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 190 275
  (Eq.refl Bool.true) (allA_of_3_0 86 190 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 189 275 (Eq.refl
  Bool.true) (allA_succ_of_accept 86 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 189 275 (accept_3_2 85 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 189 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 189 275
  (Polychromatic418967fa.accept_13_5_7_2_1_852 83 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 189 275 (accept_3_2 82 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 189 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 189 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 189 275 (accept_3_2 79 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 189 275
  (Polychromatic418967fa.accept_29_19_15_14_1_16936 77 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 189 275 (accept_3_2 76 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 189 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 189 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 189 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 189 275 (accept_3_2 73 189 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 189 275 (Polychromatic418967fa.accept_14_2_7_9_1_2937
  72 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 189 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 71 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 189 275 (accept_3_2 70 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 189 275 (Polychromatic418967fa.accept_17_1_2_3_1_4668 69 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 189 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 189 275 (accept_3_2 67 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 189 275
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 65 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 189 275 (accept_3_2 64 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 189 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 189 275 (accept_3_2 61 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 189 275 (Polychromatic418967fa.accept_13_8_7_2_1_2988 60 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 189 275
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 59 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 189 275 (accept_3_2 58 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 189 275 (Polychromatic418967fa.accept_13_5_7_2_1_852 57 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 189 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 189 275 (accept_3_2 55 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 189 275
  (Polychromatic418967fa.accept_19_15_18_9_1_8869 53 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 189 275 (accept_3_2 52 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 189 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 189 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 189 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 189 275 (accept_3_2 49 189 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 189 275 (Polychromatic418967fa.accept_13_9_7_2_1_3869
  48 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 275
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 47 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 275 (accept_3_2 46 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 189 275 (Polychromatic418967fa.accept_17_11_2_3_1_8468 45 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 189 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 275 (accept_3_2 43 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 189 275 (accept_3_2 40 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 189 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 275 (accept_3_2 37 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 275 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 275
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 189 275 (accept_3_2 34 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 189 275 (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 275 (accept_3_2 31 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 275
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 29 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 275 (accept_3_2 28 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 189 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 275 (accept_3_2 25 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 275 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 275
  (Polychromatic418967fa.accept_20_3_9_15_1_6847 23 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 275 (accept_3_2 22 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 189 275 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 189 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 275 (accept_3_2 19 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 275
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 17 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 275 (accept_3_2 16 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 275 (accept_3_2 13 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 275 (Polychromatic418967fa.accept_14_12_7_9_1_726 12 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 275
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 275 (accept_3_2 10 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 275 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 275 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 275 (accept_3_2 7 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 189 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 275
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 275 (accept_3_2 4 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 275 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 189 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 275 (accept_3_2 1 189 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 189
  275))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 188 275
  (Eq.refl Bool.true) (allA_succ_of_accept 87 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 188 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 86 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 188 275 (accept_3_2 85 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 188 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 188 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 188 275 (accept_3_2 82 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 188 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 80 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 188 275 (accept_3_2 79 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 188 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 188 275 (Polychromatic418967fa.accept_10_7_8_5_1_1008 77 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 188 275 (accept_3_2 76 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 188 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 188 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 74 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 188 275 (accept_3_2 73 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 188 275 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 188 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 188 275 (accept_3_2 70 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 188 275
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 68 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 188 275 (accept_3_2 67 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 188 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 188 275 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 188 275 (accept_3_2 64 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 188 275
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 188 275 (accept_3_2 61 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 188 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 188 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 188 275 (accept_3_2 58 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 188 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 188 275 (accept_3_2 55 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 188 275 (Polychromatic418967fa.accept_20_14_8_15_1_8432 54 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 188 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 188 275 (accept_3_2 52 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 188 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 188 275 (accept_3_2 49 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 188 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 188 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 188 275 (accept_3_2 46 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 188 275
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 44 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 188 275 (accept_3_2 43 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 188 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 188 275 (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 188 275 (accept_3_2 40 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 188 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 188 275
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 188 275 (accept_3_2 37 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 188 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 188 275 (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 188 275 (accept_3_2 34 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 188 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 188 275
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 188 275 (accept_3_2 31 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 188 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 188 275 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 188 275 (accept_3_2 28 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 188 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 188 275 (accept_3_2 25 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 188 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 188 275 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 188 275 (accept_3_2 22 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 188 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 188 275 (accept_3_2 19 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 188 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 188 275 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 188 275 (accept_3_2 16 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 188 275
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 188 275 (accept_3_2 13 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 188 275 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 188 275 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 188 275 (accept_3_2 10 188 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 188 275
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 188 275 (accept_3_2 7 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  188 275 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 188 275 (Polychromatic418967fa.accept_20_5_8_15_1_9845 5 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 188 275 (accept_3_2 4 188 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 188 275 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 275
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 188 275 (accept_3_2 1 188 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 187 275
  (Eq.refl Bool.true) (allA_of_3_0 89 187 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 186 275 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 186 275 (accept_3_2 88 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 186 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 87 186 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 186 275
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 86 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 186 275 (accept_3_2 85 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 186 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 186 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 186 275 (accept_3_2 82 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 186 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 80 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 186 275 (accept_3_2 79 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 186 275 (Polychromatic418967fa.accept_15_3_6_5_1_2079 78 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 186 275 (accept_3_2 76 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 186 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 186 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 74 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 186 275 (accept_3_2 73 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 186 275 (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 186 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 186 275 (accept_3_2 70 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 186 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 186 275 (accept_3_2 67 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 186 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 186 275 (accept_3_2 64 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 186 275 (Polychromatic418967fa.accept_13_11_4_2_1_2954 63 186 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 186 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 186 275 (accept_3_2 61 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 186 275 (Polychromatic418967fa.accept_16_12_10_3_1_4209 60 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 186 275 (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 186 275 (accept_3_2 58 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 186 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 186 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 186 275 (accept_3_2 55 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 186 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 186 275 (accept_3_2 52 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 186 275 (Polychromatic418967fa.accept_10_1_6_5_1_304 51 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 186 275
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 50 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 186 275 (accept_3_2 49 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 186 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 186 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 186 275 (accept_3_2 46 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 186 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 186 275 (accept_3_2 43 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 186 275 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 186 275 (accept_3_2 40 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 186 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 186 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 186 275 (accept_3_2 37 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 186 275 (Polychromatic418967fa.accept_21_15_18_2_1_6376 36 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 186 275 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 186 275 (accept_3_2 34 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 186 275
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 32 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 186 275 (accept_3_2 31 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 186 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 275 (accept_3_2 28 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 186 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 275
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 186 275 (accept_3_2 25 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 186 275 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 186 275 (Polychromatic418967fa.accept_16_7_10_3_1_2210 23 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 275 (accept_3_2 22 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 186 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 275
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 186 275 (accept_3_2 19 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 186 275 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 275 (accept_3_2 16 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 186 275 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 186 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 275
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 186 275 (accept_3_2 13 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 186 275 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 186 275 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 275 (accept_3_2 10 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 275
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 186 275 (accept_3_2 7 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  186 275 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 186 275 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 275 (accept_3_2 4 186 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 186 275 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 186 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 275
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 186 275 (accept_3_2 1 186 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 185 275
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 185 275 5 18 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 185 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 185 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 185 275 (accept_3_2 88 185 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 185 275 (Polychromatic418967fa.accept_13_9_3_2_1_399
  87 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 185 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 185 275 5 17 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 84 185 275 (Polychromatic418967fa.accept_19_8_14_9_1_4590 84 185 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 185 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 185 275 (accept_3_2 82 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 185 275 (Polychromatic418967fa.accept_19_5_14_9_1_4554 81 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 185 275 5 16 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 185 275 (accept_3_2 79 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 185 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 185 275 (Polychromatic418967fa.accept_13_12_3_2_1_1470 77 185
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 185 275 (accept_3_2 76 185
  275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 185 275 5 15 37 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 185 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 185 275 (accept_3_2 73 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 185 275 (Polychromatic418967fa.accept_20_12_5_15_1_14100 72 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 185 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 185 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 185 275 5 14 37 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 185 275
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 185 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 185 275 (accept_3_2 67 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 185 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 185 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 185 275 5 13 37 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 185 275 (accept_3_2 64 185 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 185 275 (Polychromatic418967fa.accept_13_11_3_2_1_863 63 185
  275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 185 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 185 275 (accept_3_2 61 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  185 275 5 12 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 185 275 (Polychromatic418967fa.accept_20_19_5_15_1_5380 59 185 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 185 275 (accept_3_2 58 185 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 185 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 185 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 185 275
  (Polychromatic418967fa.accept_20_16_5_15_1_5364 56 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 185 275 5 11 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 185 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 185 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 185 275
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 53 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 185 275 (accept_3_2 52 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 185 275 (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 185 275 5 10 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 185 275 (accept_3_2 49 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 185 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 185 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 185 275 (accept_3_2 46 185 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 185 275 5 9 37 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 185 275
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 44 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 185 275 (accept_3_2 43 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 185 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 185 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 185 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 185 275 5 8 37 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 185 275
  (Polychromatic418967fa.accept_16_7_9_3_1_1324 39 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 185 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 275 (accept_3_2 37 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 185 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 185 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 185 275 5 7 37 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 185 275 (accept_3_2 34 185 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 185 275
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 275
  (Polychromatic418967fa.accept_20_12_5_15_1_14100 32 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 185 275 (accept_3_2 31 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 185 275 5 6 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 185 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 275 (accept_3_2 28 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 185 275 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 185 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 185 275 5 5 37 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 185 275
  (Polychromatic418967fa.accept_13_11_3_2_1_863 24 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 185 275 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 275 (accept_3_2 22 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 185 275 (Polychromatic418967fa.accept_20_1_5_15_1_6913 21 185 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 185 275 5 4 37 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 185 275 (accept_3_2 19 185 275
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 275
  (Polychromatic418967fa.accept_19_17_14_9_1_8833 17 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 185 275 (accept_3_2 16 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 185 275 5 3 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 185 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 275 (accept_3_2 13 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 185 275 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 185 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 275 (Polychromatic418967fa.accept_13_11_3_2_1_863
  11 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 185 275 5 2 37 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 185 275
  (Polychromatic418967fa.accept_13_9_3_2_1_399 9 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 185 275 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 275 (accept_3_2 7 185 275 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 185 275 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 185 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 185 275 5 1 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 185 275 (accept_3_2 4 185 275 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 275 (Polychromatic418967fa.accept_19_3_14_9_1_8866 3 185 275 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 275
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 275 (accept_3_2 1 185 275 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  275)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_275_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


