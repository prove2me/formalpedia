-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch279
-- name    : Polychromatic418967fa_Branch279
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:31:27.9162+00:00
-- url     : https://prove2.me/theorems/7710d74a-3ab5-464a-8a94-9220a7e497db
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch279_Segment003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_279 : allB 279 279 :=
  allB_succ' 2 278 279 (Eq.refl Bool.true) (allA_succ_of_accept 1 278 279 (accept_3_4 1 278 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 278 279)) (allB_succ' 3 277 279 (Eq.refl Bool.true) (allA_succ_of_accept 2 277 279
  (accept_3_5 2 277 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 277 279
  (Polychromatic418967fa.accept_15_1_7_9_1_20 1 277 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 277 279))) (allB_succ' 4 276 279 (Eq.refl Bool.true) (allA_succ_of_gcd 3 276 279 3 1 92 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 276 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 276 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 276 279 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 276 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 276 279)))) (allB_succ' 5 275 279 (Eq.refl Bool.true) (allA_succ_of_accept 4
  275 279 (accept_3_4 4 275 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 275 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 275 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 275 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 275 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 275 279 (accept_3_4 1 275 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 275 279))))) (allB_succ' 6 274 279 (Eq.refl Bool.true) (allA_succ_of_accept 5 274 279
  (accept_3_5 5 274 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 274 279
  (Polychromatic418967fa.accept_19_4_8_13_1_7802 4 274 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 274 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 274 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 274 279 (accept_3_5 2 274 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 274 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 274 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 274 279)))))) (allB_succ' 7 273 279 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 273 279 3 2 91 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 273 279 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 273 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 273 279 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 273 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 273 279 3 1 91 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 273 279
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 273 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 273 279 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 273 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 273 279))))))) (allB_succ' 8 272 279 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 272 279 (accept_3_4 7 272 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  272 279 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 272 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 272 279 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 272 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 272 279 (accept_3_4 4 272 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 272 279 (Polychromatic418967fa.accept_18_3_2_9_1_1013 3 272 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 272 279
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 2 272 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 272 279 (accept_3_4 1 272 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 272
  279)))))))) (allB_succ' 9 271 279 (Eq.refl Bool.true) (allA_succ_of_accept 8 271 279 (accept_3_5 8 271 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 271 279 (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 271 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 271 279
  (Polychromatic418967fa.accept_14_6_5_13_1_367 6 271 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 271 279 (accept_3_5 5 271 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  271 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 271 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 271 279 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 271 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 271 279 (accept_3_5 2 271 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 271 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 271 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 271 279))))))))) (allB_succ' 10 270 279 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 270 279 9 1 30 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 270 279 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 270 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 270 279 (Polychromatic418967fa.accept_19_7_4_13_1_6319
  7 270 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 270 279 3 2 90 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 270 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 270 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 270 279 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 270 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 270 279 3 1 90 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 270 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 270 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 270 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 270 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 270 279)))))))))) (allB_succ' 11 269 279 (Eq.refl Bool.true) (allA_succ_of_accept 10 269 279 (accept_3_4 10
  269 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 269 279
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 269 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 269 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 269 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 269 279 (accept_3_4 7 269 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 269 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 269 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 269 279 (Polychromatic418967fa.accept_15_5_14_9_1_274
  5 269 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 269 279 (accept_3_4 4
  269 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 269 279
  (Polychromatic418967fa.accept_13_3_9_6_1_502 3 269 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 269 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 269 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 269 279 (accept_3_4 1 269 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 269 279))))))))))) (allB_succ' 12 268 279 (Eq.refl Bool.true) (allA_succ_of_accept 11 268 279
  (accept_3_5 11 268 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 268 279
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 268 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 268 279 (Polychromatic418967fa.accept_20_9_8_19_1_802 9 268 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 268 279 (accept_3_5 8 268 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 268 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 268 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 268 279 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  268 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 268 279 (accept_3_5 5 268
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 268 279
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 268 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 268 279 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 268 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 268 279 (accept_3_5 2 268 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 268 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 268 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 268 279)))))))))))) (allB_succ' 13 267 279 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 267 279 3 4 89 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 267 279 (Polychromatic418967fa.accept_18_11_15_9_1_360 11 267 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 267 279 (Polychromatic418967fa.accept_15_10_12_9_1_776 10 267
  279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 267 279 3 3 89 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 267 279
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 267 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 267 279 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 267 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 267 279 3 2 89 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 267 279 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 267 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 267 279
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 267 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 267 279 3 1 89 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 267 279 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 267 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 279 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 267 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 267 279))))))))))))) (allB_succ' 14 266 279
  (Eq.refl Bool.true) (allA_succ_of_accept 13 266 279 (accept_3_4 13 266 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 266 279 (Polychromatic418967fa.accept_21_12_14_6_1_8214 12 266 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 266 279 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  266 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 266 279 (accept_3_4 10
  266 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 266 279
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 266 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 266 279 (Polychromatic418967fa.accept_21_8_14_6_1_9800 8 266 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 266 279 (accept_3_4 7 266 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 266 279 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 266 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 266 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  266 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 266 279 (accept_3_4 4 266
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 266 279
  (Polychromatic418967fa.accept_10_3_6_9_1_779 3 266 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 266 279 (Polychromatic418967fa.accept_15_2_11_9_1_263 2 266 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 266 279 (accept_3_4 1 266 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 266 279)))))))))))))) (allB_succ' 15 265 279 (Eq.refl Bool.true) (allA_succ_of_accept 14 265 279
  (accept_3_5 14 265 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 265 279
  (Polychromatic418967fa.accept_16_13_9_7_1_4532 13 265 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 265 279 (Polychromatic418967fa.accept_13_12_5_6_1_1050 12 265 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 265 279 (accept_3_5 11 265 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 265 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 265 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 265 279 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  265 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 265 279 (accept_3_5 8 265
  279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 265 279
  (Polychromatic418967fa.accept_21_7_13_6_1_349 7 265 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 265 279 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 265 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 265 279 (accept_3_5 5 265 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 265 279 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 265 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 265 279 (Polychromatic418967fa.accept_13_3_5_6_1_3192
  3 265 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 265 279 (accept_3_5 2
  265 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 265 279
  (Polychromatic418967fa.accept_10_1_5_9_1_157 1 265 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 265 279))))))))))))))) (allB_succ' 16 264 279 (Eq.refl Bool.true) (allA_succ_of_gcd 15 264 279 3 5 88 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 264 279
  (Polychromatic418967fa.accept_20_14_4_19_1_4288 14 264 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 264 279 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 264 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 264 279 3 4 88 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 264 279
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 264 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 264 279 (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 264 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 264 279 3 3 88 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 264 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 264 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 264 279
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 264 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 264 279 3 2 88 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 264 279 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 264 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 264 279 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 264 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 264 279 3 1 88 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 264 279
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 2 264 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 264 279 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 264 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 264 279)))))))))))))))) (allB_succ' 17 263 279 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 263 279 (accept_3_4 16 263 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 263 279 (Polychromatic418967fa.accept_18_15_11_9_1_4256 15 263 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 263 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 263 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 263 279 (accept_3_4 13 263 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 263 279 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 263 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 263 279
  (Polychromatic418967fa.accept_19_11_16_13_1_4853 11 263 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 263 279 (accept_3_4 10 263 279 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 263 279 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 263 279 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 263 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 263 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 263 279 (accept_3_4 7 263 279
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 263 279 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  6 263 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 263 279
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 263 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 263 279 (accept_3_4 4 263 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  263 279 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 263 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 263 279 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 263 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 263 279 (accept_3_4 1 263 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 263 279))))))))))))))))) (allB_succ' 18 262 279 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 262 279 (accept_3_5 17 262 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 262 279 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 262 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 262 279 (Polychromatic418967fa.accept_16_15_6_7_1_4512 15 262 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 262 279 (accept_3_5 14 262 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 262 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 262 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 262 279
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 262 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 262 279 (accept_3_5 11 262 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 262 279 (Polychromatic418967fa.accept_13_10_2_6_1_1044 10 262 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 262 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 262 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 262 279 (accept_3_5 8 262 279 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 262 279 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 262 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 262 279
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 262 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 262 279 (accept_3_5 5 262 279 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  262 279 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 262 279 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 262 279 (Polychromatic418967fa.accept_14_3_10_13_1_339 3 262 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 262 279 (accept_3_5 2 262 279 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 262 279 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 262 279
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 262 279))))))))))))))))))
  (Polychromatic418967fa.branch_279_segment_003)))))))))))))))))


