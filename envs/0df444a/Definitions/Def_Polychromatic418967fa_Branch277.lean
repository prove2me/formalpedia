-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch277
-- name    : Polychromatic418967fa_Branch277
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:33:43.080839+00:00
-- url     : https://prove2.me/theorems/75011154-b166-4e74-8712-4091201c2b64
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch277_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_277 : allB 277 277 :=
  allB_succ' 2 276 277 (Eq.refl Bool.true) (allA_succ_of_accept 1 276 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  276 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 276 277)) (allB_succ' 3 275 277
  (Eq.refl Bool.true) (allA_of_3_1 3 275 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 274 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 274 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 274 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 274 277 (accept_3_3 2 274 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 274 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 274 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 274 277)))) (allB_succ' 5 273 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 273 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 273 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 273 277 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 273 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 273 277 (accept_3_3 2 273 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 273 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 1
  273 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 273 277))))) (allB_succ' 6 272 277
  (Eq.refl Bool.true) (allA_of_3_1 6 272 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 271 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 271 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 271 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 271 277 (accept_3_3 5 271 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 271 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 271 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 271 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 271 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 271 277 (accept_3_3 2 271 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  271 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 271 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 271 277))))))) (allB_succ' 8 270 277 (Eq.refl Bool.true) (allA_succ_of_accept 7 270 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 270 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 270 277 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 270 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 270 277 (accept_3_3 5 270 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 270 277 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 270 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 270 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  270 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 270 277 (accept_3_3 2 270
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 270 277
  (Polychromatic418967fa.accept_13_1_10_4_1_954 1 270 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 270 277)))))))) (allB_succ' 9 269 277 (Eq.refl Bool.true) (allA_of_3_1 9 269 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 268 277 (Eq.refl Bool.true) (allA_succ_of_accept 9 268 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 268 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 268 277 (accept_3_3 8 268 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  268 277 (Polychromatic418967fa.accept_16_7_12_5_1_734 7 268 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 268 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 268 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 268 277 (accept_3_3 5 268 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 268 277 (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 268 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 268 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 268 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 268 277 (accept_3_3 2 268 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  268 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 268 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 268 277)))))))))) (allB_succ' 11 267 277 (Eq.refl Bool.true) (allA_succ_of_accept 10 267 277
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 267 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 267 277 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 267 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 267 277 (accept_3_3 8 267 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 267 277 (Polychromatic418967fa.accept_16_7_11_5_1_4402 7 267 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 267 277
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 267 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 267 277 (accept_3_3 5 267 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  267 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 267 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 267 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 267 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 267 277 (accept_3_3 2 267 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 267 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 267 277))))))))))) (allB_succ' 12 266 277 (Eq.refl
  Bool.true) (allA_of_3_1 12 266 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 265 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 265 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 265 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 265 277 (accept_3_3 11 265 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 265 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 265 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 265 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 9
  265 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 265 277 (accept_3_3 8 265
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 265 277
  (Polychromatic418967fa.accept_19_7_18_11_1_464 7 265 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 265 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 265 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 265 277 (accept_3_3 5 265 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 265 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 265 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 265 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 3
  265 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 265 277 (accept_3_3 2 265
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 265 277 (Polychromatic418967fa.accept_9_1_4_7_1_7
  1 265 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 265 277))))))))))))) (allB_succ' 14
  264 277 (Eq.refl Bool.true) (allA_succ_of_accept 13 264 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 264 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 264 277
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 264 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 264 277 (accept_3_3 11 264 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 264 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 264 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 264 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 264 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 264 277 (accept_3_3 8 264 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 264 277 (Polychromatic418967fa.accept_17_7_9_5_1_2588 7 264 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 264 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 264 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 264 277 (accept_3_3 5 264 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  264 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 264 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 264 277 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 264 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 264 277 (accept_3_3 2 264 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 264 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 264 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 264 277)))))))))))))) (allB_succ' 15 263 277 (Eq.refl
  Bool.true) (allA_of_3_1 15 263 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 262 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 262 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 262 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 262 277 (accept_3_3 14 262 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 262 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 262 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 262 277 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  262 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 262 277 (accept_3_3 11
  262 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 262 277
  (Polychromatic418967fa.accept_19_10_15_11_1_3421 10 262 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 262 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 262 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 262 277 (accept_3_3 8 262 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 262 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 262 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 262 277
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 262 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 262 277 (accept_3_3 5 262 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  262 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 262 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 262 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 262 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 262 277 (accept_3_3 2 262 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 262 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 262 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 262 277)))))))))))))))) (allB_succ' 17 261 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 261 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 261 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 261 277 (Polychromatic418967fa.accept_12_3_9_1_1_290
  15 261 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 261 277 (accept_3_3 14
  261 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 261 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 261 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 261 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 261 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 261 277 (accept_3_3 11 261 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 261 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 261 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 261 277
  (Polychromatic418967fa.accept_19_9_14_11_1_7496 9 261 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 261 277 (accept_3_3 8 261 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  261 277 (Polychromatic418967fa.accept_19_7_14_11_1_4724 7 261 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 261 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 261 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 261 277 (accept_3_3 5 261 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 261 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 261 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 261 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 261 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 261 277 (accept_3_3 2 261 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  261 277 (Polychromatic418967fa.accept_15_1_6_7_1_6282 1 261 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 261 277))))))))))))))))) (allB_succ' 18 260 277 (Eq.refl Bool.true) (allA_of_3_1 18 260 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 259 277 (Eq.refl Bool.true) (allA_succ_of_accept 18 259 277
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 259 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 259 277 (accept_3_3 17 259 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 259 277 (Polychromatic418967fa.accept_13_3_12_4_1_110 16 259 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 259 277 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 259 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 259 277 (accept_3_3 14 259 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 259 277 (Polychromatic418967fa.accept_19_13_12_11_1_1249 13 259 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 259 277
  (Polychromatic418967fa.accept_10_2_9_7_1_720 12 259 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 259 277 (accept_3_3 11 259 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 259 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 259 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 259 277 (Polychromatic418967fa.accept_27_9_16_7_1_9526 9 259 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 259 277 (accept_3_3 8 259 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 259 277 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 259 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 259 277
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 259 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 259 277 (accept_3_3 5 259 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  259 277 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 259 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 259 277 (Polychromatic418967fa.accept_13_3_12_4_1_110 3 259 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 259 277 (accept_3_3 2 259 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 259 277 (Polychromatic418967fa.accept_17_1_4_5_1_3501 1 259 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 259 277))))))))))))))))))) (allB_succ' 20 258 277
  (Eq.refl Bool.true) (allA_succ_of_accept 19 258 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 258 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 258 277
  (Polychromatic418967fa.accept_21_18_6_4_1_5031 18 258 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 258 277 (accept_3_3 17 258 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 258 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 258 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 258 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 258 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 258 277 (accept_3_3 14 258 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 258 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 258 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 258 277
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 258 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 258 277 (accept_3_3 11 258 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 258 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 258 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 258 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 258 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 258 277 (accept_3_3 8 258 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 258 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 258 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 258 277
  (Polychromatic418967fa.accept_13_6_11_4_1_938 6 258 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 258 277 (accept_3_3 5 258 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  258 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 258 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 258 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 258 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 258 277 (accept_3_3 2 258 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 258 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 258 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 258 277)))))))))))))))))))) (allB_succ' 21 257 277
  (Eq.refl Bool.true) (allA_of_3_1 21 257 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 256 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 256 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 256 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 256 277 (accept_3_3 20 256 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 256 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 256 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 256 277
  (Polychromatic418967fa.accept_13_5_9_4_1_441 18 256 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 256 277 (accept_3_3 17 256 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 256 277 (Polychromatic418967fa.accept_17_16_1_5_1_2600 16 256 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 256 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 256 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 256 277 (accept_3_3 14 256 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 256 277 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 256 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 256 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 256 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 256 277 (accept_3_3 11 256 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 256 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 256 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 256 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 256 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 256 277 (accept_3_3 8 256 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 256 277 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 256 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 256 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 256 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 256 277 (accept_3_3 5 256 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  256 277 (Polychromatic418967fa.accept_17_4_1_5_1_2554 4 256 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 256 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 256 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 256 277 (accept_3_3 2 256 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 256 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 256 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 256 277)))))))))))))))))))))) (allB_succ' 23 255 277
  (Eq.refl Bool.true) (allA_succ_of_accept 22 255 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 255 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 255 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 255 277 (accept_3_3 20 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 255 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 255 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 255 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 255 277 (accept_3_3 17 255 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 255 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 255 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 255 277
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 255 277 (accept_3_3 14 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 255 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 255 277 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 255 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 255 277 (accept_3_3 11 255 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 255 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 255 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 255 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 255 277 (accept_3_3 8 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  255 277 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 255 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 255 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 255 277 (accept_3_3 5 255 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 255 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 255 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 277
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 255 277 (accept_3_3 2 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  255 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 255 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 255 277))))))))))))))))))))))) (allB_succ' 24 254 277 (Eq.refl Bool.true) (allA_of_3_1 24 254
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 253 277 (Eq.refl Bool.true) (allA_succ_of_accept 24 253
  277 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 253 277 (accept_3_3 23 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 253 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 253 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 253 277 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 253 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 253 277 (accept_3_3 20 253 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 253 277 (Polychromatic418967fa.accept_7_5_1_4_1_122
  19 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 253 277
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 253 277 (accept_3_3 17 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 253 277 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 253 277 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 253 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 253 277 (accept_3_3 14 253 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 253 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 253 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 253 277
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 253 277 (accept_3_3 11 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 253 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 253 277 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 253 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 253 277 (accept_3_3 8 253 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 253 277 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 253 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 253 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 253 277 (accept_3_3 5 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  253 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 253 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 253 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 253 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 253 277 (accept_3_3 2 253 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 253 277 (Polychromatic418967fa.accept_16_1_13_5_1_2280 1 253 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 253 277))))))))))))))))))))))))) (allB_succ' 26 252 277
  (Eq.refl Bool.true) (allA_succ_of_accept 25 252 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 252 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 252 277
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 252 277 (accept_3_3 23 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 252 277 (Polychromatic418967fa.accept_13_9_5_4_1_1591 22 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 252 277 (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 252 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 252 277 (accept_3_3 20 252 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 252 277 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 252
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 252 277
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 252 277 (accept_3_3 17 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 252 277 (Polychromatic418967fa.accept_19_16_5_11_1_4743 16 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 252 277 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 252 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 252 277 (accept_3_3 14 252 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 252 277 (Polychromatic418967fa.accept_19_13_5_11_1_7653 13 252
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 252 277
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 252 277 (accept_3_3 11 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 252 277 (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 252 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 252 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 252 277 (accept_3_3 8 252 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 252 277 (Polychromatic418967fa.accept_16_7_12_5_1_734 7 252 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 252 277
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 6 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 252 277 (accept_3_3 5 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  252 277 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 252 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 252 277 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 252 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 252 277 (accept_3_3 2 252 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 252 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 252 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252 277)))))))))))))))))))))))))) (allB_succ'
  27 251 277 (Eq.refl Bool.true) (allA_of_3_1 27 251 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 250 277
  (Eq.refl Bool.true) (allA_succ_of_accept 27 250 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 250 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 250 277 (accept_3_3 26 250 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 250 277 (Polychromatic418967fa.accept_13_12_3_4_1_928 25 250
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 250 277
  (Polychromatic418967fa.accept_17_7_12_5_1_1580 24 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 250 277 (accept_3_3 23 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 250 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 250 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 250 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 250 277 (accept_3_3 20 250 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 250 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 250 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 250 277
  (Polychromatic418967fa.accept_15_3_10_7_1_2196 18 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 250 277 (accept_3_3 17 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 250 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 250 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 250 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 250 277 (accept_3_3 14 250 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 250 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 250 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 250 277
  (Polychromatic418967fa.accept_13_12_3_4_1_928 12 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 250 277 (accept_3_3 11 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 250 277 (Polychromatic418967fa.accept_17_10_12_5_1_6028 10 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 250 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 250 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 250 277 (accept_3_3 8 250 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 250 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 250 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 250 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 250 277 (accept_3_3 5 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  250 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 250 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 250 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 250 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 250 277 (accept_3_3 2 250 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 250 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 250 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 250 277)))))))))))))))))))))))))))) (allB_succ' 29 249
  277 (Eq.refl Bool.true) (allA_succ_of_accept 28 249 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 249 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 249 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 249 277 (accept_3_3 26 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 249 277 (Polychromatic418967fa.accept_13_12_2_4_1_3131 25 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 249 277 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 249 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 249 277 (accept_3_3 23 249 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 249 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 249 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 249 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 249 277 (accept_3_3 20 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 249 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 249 277 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 249 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 249 277 (accept_3_3 17 249 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 249 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 249 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 249 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 249 277 (accept_3_3 14 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 249 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 249 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 249 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 249 277 (accept_3_3 11 249 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 249 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 249 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 249 277
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 249 277 (accept_3_3 8 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  249 277 (Polychromatic418967fa.accept_17_7_11_5_1_3539 7 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 249 277 (Polychromatic418967fa.accept_13_6_2_4_1_923 6 249 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 277 (accept_3_3 5 249 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 249 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 249 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 249 277 (accept_3_3 2 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  249 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 249 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 249 277))))))))))))))))))))))))))))) (allB_succ' 30 248 277 (Eq.refl Bool.true) (allA_of_3_1 30
  248 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 247 277 (Eq.refl Bool.true) (allA_succ_of_accept 30
  247 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 247 277 (accept_3_3 29 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 247 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 247 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 247 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 247 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 247 277 (accept_3_3 26 247 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 247 277
  (Polychromatic418967fa.accept_23_2_17_1_1_16972 25 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 247 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 247 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 247 277 (accept_3_3 23 247 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 247 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 247 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 247 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 247 277 (accept_3_3 20 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 247 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 247 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 247 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 247 277 (accept_3_3 17 247 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 247 277 (Polychromatic418967fa.accept_14_2_9_11_1_3054 16 247 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 247 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 247 277 (accept_3_3 14 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 247 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 247 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 247 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 247 277 (accept_3_3 11 247 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 247 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 247 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 247 277
  (Polychromatic418967fa.accept_20_9_7_17_1_1655 9 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 247 277 (accept_3_3 8 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  247 277 (Polychromatic418967fa.accept_17_7_9_5_1_2588 7 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 247 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 247 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 247 277 (accept_3_3 5 247 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 247 277 (Polychromatic418967fa.accept_18_4_13_7_1_5395 4 247 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 247 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 247 277 (accept_3_3 2 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  247 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 247 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 247 277))))))))))))))))))))))))))))))) (allB_succ' 32 246 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 246 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 246 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 246 277 (Polychromatic418967fa.accept_17_13_8_5_1_3532 30 246
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 246 277 (accept_3_3 29 246
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 246 277 (Polychromatic418967fa.accept_9_1_3_7_1_6
  28 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 246 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 246 277 (accept_3_3 26 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 246 277 (Polychromatic418967fa.accept_19_6_18_11_1_7636 25 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 246 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 246 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 246 277 (accept_3_3 23 246 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 246 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 246 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 246 277
  (Polychromatic418967fa.accept_10_1_6_7_1_710 21 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 246 277 (accept_3_3 20 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 246 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 246 277 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 246 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 246 277 (accept_3_3 17 246 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 246 277 (Polychromatic418967fa.accept_13_3_12_4_1_110 16 246
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 246 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 246 277 (accept_3_3 14 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 246 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 246 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 246 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 246 277 (accept_3_3 11 246 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 246 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 246 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 246 277
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 246 277 (accept_3_3 8 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  246 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 246 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 246 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 246 277 (accept_3_3 5 246 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 246 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 246 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 246 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 246 277 (accept_3_3 2 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  246 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 246 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 246 277)))))))))))))))))))))))))))))))) (allB_succ' 33 245 277 (Eq.refl Bool.true) (allA_of_3_1
  33 245 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 244 277 (Eq.refl Bool.true) (allA_succ_of_accept 33
  244 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 244 277 (accept_3_3 32 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 244 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 244 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 244 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 244 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 244 277 (accept_3_3 29 244 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 244 277
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 244 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 244 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 244 277 (accept_3_3 26 244 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 244 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 244 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 244 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  244 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 244 277 (accept_3_3 23
  244 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 244 277
  (Polychromatic418967fa.accept_9_4_1_7_1_293 22 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 244 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 244 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 244 277 (accept_3_3 20 244 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 244 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 244 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 244 277
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 244 277 (accept_3_3 17 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 244 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 244 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 244 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 244 277 (accept_3_3 14 244 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 244 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 244 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 244 277
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 244 277 (accept_3_3 11 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 244 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 244 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 244 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 244 277 (accept_3_3 8 244 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 244 277 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 244 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 244 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 244 277 (accept_3_3 5 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  244 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 244 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 244 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 244 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 244 277 (accept_3_3 2 244 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 244 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 244 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 277)))))))))))))))))))))))))))))))))) (allB_succ' 35
  243 277 (Eq.refl Bool.true) (allA_succ_of_accept 34 243 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 243 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 243 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 243 277 (accept_3_3 32 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 243 277 (Polychromatic418967fa.accept_13_5_9_4_1_441 31 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 243 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 243 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 243 277 (accept_3_3 29 243 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 243 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 243 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 243 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 243 277 (accept_3_3 26 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 243 277 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 243 277 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 243 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 243 277 (accept_3_3 23 243 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 243 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 243 277
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 243 277 (accept_3_3 20 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 243 277 (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 243 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 243 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 243 277 (accept_3_3 17 243 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 243 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 277
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 243 277 (accept_3_3 14 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 243 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 243 277 (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 243 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 243 277 (accept_3_3 11 243 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 243 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 277
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 243 277 (accept_3_3 8 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  243 277 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 243 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 243 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 277 (accept_3_3 5 243 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 243 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 277
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 243 277 (accept_3_3 2 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  243 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 243 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 243 277))))))))))))))))))))))))))))))))))) (allB_succ' 36 242 277 (Eq.refl Bool.true)
  (allA_of_3_1 36 242 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 241 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 241 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 241 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 241 277 (accept_3_3 35 241 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 241 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 241 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 241 277
  (Polychromatic418967fa.accept_23_10_11_1_1_15538 33 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 241 277 (accept_3_3 32 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 241 277 (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 241 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 241 277 (Polychromatic418967fa.accept_20_10_1_17_1_8614 30 241
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 241 277 (accept_3_3 29 241
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 241 277
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 241 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 241 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 241 277 (accept_3_3 26 241 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 241 277 (Polychromatic418967fa.accept_13_12_7_4_1_3124 25 241 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 241 277
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 241 277 (accept_3_3 23 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 241 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 241 277 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 241 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 241 277 (accept_3_3 20 241 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 241 277 (Polychromatic418967fa.accept_13_6_7_4_1_2264 19 241
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 241 277
  (Polychromatic418967fa.accept_20_18_1_17_1_4085 18 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 241 277 (accept_3_3 17 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 241 277 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 241 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 241 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 241 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 241 277 (accept_3_3 14 241 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 241 277 (Polychromatic418967fa.accept_7_6_3_4_1_294
  13 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 241 277
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 241 277 (accept_3_3 11 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 241 277 (Polychromatic418967fa.accept_13_10_7_4_1_2262 10 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 241 277 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 241 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 277 (accept_3_3 8 241 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 277 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 241 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 241 277
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 277 (accept_3_3 5 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 241 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 277 (Polychromatic418967fa.accept_13_3_7_4_1_435 3 241 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 277 (accept_3_3 2 241 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 241 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 277))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 240 277 (Eq.refl Bool.true) (allA_succ_of_accept 37 240 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 240 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 240 277
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 240 277 (accept_3_3 35 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 240 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 240 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 240 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 240 277 (accept_3_3 32 240 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 240 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 240 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 240 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 240 277 (accept_3_3 29 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 240 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 240 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 240 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 240 277 (accept_3_3 26 240 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 240 277 (Polychromatic418967fa.accept_27_25_24_7_1_17038 25 240 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 240 277
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 240 277 (accept_3_3 23 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 240 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 240 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 240 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 240 277 (accept_3_3 20 240 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 240 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 240 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 240 277
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 240 277 (accept_3_3 17 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 240 277 (Polychromatic418967fa.accept_17_16_2_5_1_6031 16 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 240 277 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 240 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 240 277 (accept_3_3 14 240 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 240 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 240 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 240 277
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 240 277 (accept_3_3 11 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 240 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 240 277 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 240 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 240 277 (accept_3_3 8 240 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 240 277 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 240 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 240 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 240 277 (accept_3_3 5 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  240 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 240 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 240 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 240 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 240 277 (accept_3_3 2 240 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 240 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 277))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 239 277 (Eq.refl Bool.true) (allA_of_3_1 39 239 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 238 277 (Eq.refl Bool.true) (allA_succ_of_accept 39 238 277 (Polychromatic418967fa.accept_4_3_2_1_1_50
  39 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 238 277 (accept_3_3 38
  238 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 238 277
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 238 277 (Polychromatic418967fa.accept_15_6_13_7_1_222 36 238 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 238 277 (accept_3_3 35 238 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 238 277 (Polychromatic418967fa.accept_18_16_4_7_1_2927 34 238 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 238 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 238 277 (accept_3_3 32 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 238 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 238 277 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 238 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 238 277 (accept_3_3 29 238 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 238 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 238 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 238 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 238 277 (accept_3_3 26 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 238 277 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 238 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 238 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 238 277 (accept_3_3 23 238 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 238 277 (Polychromatic418967fa.accept_19_3_10_11_1_7669 22 238 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 238 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 238 277 (accept_3_3 20 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 238 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 238 277 (Polychromatic418967fa.accept_19_18_10_11_1_6058 18 238 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 238 277 (accept_3_3 17 238 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 238 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 238
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 238 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 238 277 (accept_3_3 14 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 238 277 (Polychromatic418967fa.accept_18_13_4_7_1_4086 13 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 238 277 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 238 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 238 277 (accept_3_3 11 238 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 238 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 238 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 238 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 238 277 (accept_3_3 8 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  238 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 238 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 238 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 238 277 (accept_3_3 5 238 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 238 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 238 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 238 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 238 277 (accept_3_3 2 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  238 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 238 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 238 277)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 237 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 237 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 237 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 237 277 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 237
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 237 277 (accept_3_3 38 237
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 237 277
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 237 277 (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 237 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 237 277 (accept_3_3 35 237 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 237 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 237 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 237 277 (Polychromatic418967fa.accept_7_5_6_4_1_117
  33 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 237 277 (accept_3_3 32
  237 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 237 277
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 237 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 237 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 237 277 (accept_3_3 29 237 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 237 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 237 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 237 277 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 237 277 (accept_3_3 26
  237 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 237 277
  (Polychromatic418967fa.accept_13_12_3_4_1_928 25 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 237 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 237 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 237 277 (accept_3_3 23 237 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 237 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 237 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 277
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 237 277 (accept_3_3 20 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 237 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 237 277 (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 237 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 237 277 (accept_3_3 17 237 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 237 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 237 277 (accept_3_3 14 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 237 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 237 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 237 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 277 (accept_3_3 11 237 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 237 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 277
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 237 277 (accept_3_3 8 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  237 277 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 237 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 237 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 277 (accept_3_3 5 237 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 237 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 277
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 237 277 (accept_3_3 2 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  237 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 237 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 237 277))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 236 277 (Eq.refl Bool.true)
  (allA_of_3_1 42 236 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 235 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 42 235 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 235 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 235 277 (accept_3_3 41 235 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 235 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 235 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 235 277 (Polychromatic418967fa.accept_9_3_1_7_1_97 39
  235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 235 277 (accept_3_3 38
  235 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 235 277
  (Polychromatic418967fa.accept_19_18_7_11_1_7552 37 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 235 277 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 235 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 235 277 (accept_3_3 35 235 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 235 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 235 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 235 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 235 277 (accept_3_3 32 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 235 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 235 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 235 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 235 277 (accept_3_3 29 235 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 235 277 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 235 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 235 277
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 235 277 (accept_3_3 26 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 235 277 (Polychromatic418967fa.accept_16_9_11_5_1_2279 25 235 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 235 277 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 235 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 235 277 (accept_3_3 23 235 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 235 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 235 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 235 277 (accept_3_3 20 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 235 277 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 235 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 235 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 235 277 (accept_3_3 17 235 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 235 277 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 235 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 235 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 235 277 (accept_3_3 14 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 235 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 235 277 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 235 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 235 277 (accept_3_3 11 235 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 235 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 235 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 235 277
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 235 277 (accept_3_3 8 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  235 277 (Polychromatic418967fa.accept_16_7_11_5_1_4402 7 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 235 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 235 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 235 277 (accept_3_3 5 235 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 235 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 235 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 235 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 235 277 (accept_3_3 2 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  235 277 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 235 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 235 277))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 234 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 234 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 234 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 234 277 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 234
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 234 277 (accept_3_3 41 234
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 234 277
  (Polychromatic418967fa.accept_22_18_14_13_1_12531 40 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 234 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 234 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 234 277 (accept_3_3 38 234 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 234 277 (Polychromatic418967fa.accept_19_18_6_11_1_7696 37 234 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 234 277
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 234 277 (accept_3_3 35 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 234 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 234 277 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 234 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 234 277 (accept_3_3 32 234 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 234 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 234 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 234 277
  (Polychromatic418967fa.accept_16_14_10_5_1_1393 30 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 234 277 (accept_3_3 29 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 234 277 (Polychromatic418967fa.accept_15_13_9_7_1_2194 28 234 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 234 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 234 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 234 277 (accept_3_3 26 234 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 234 277
  (Polychromatic418967fa.accept_17_8_13_5_1_1597 25 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 234 277 (Polychromatic418967fa.accept_19_5_6_11_1_6069 24 234 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 234 277 (accept_3_3 23 234 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 234 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 234 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 234 277 (Polychromatic418967fa.accept_10_1_4_7_1_374
  21 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 234 277 (accept_3_3 20
  234 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 234 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 234 277 (Polychromatic418967fa.accept_19_18_6_11_1_7696 18 234 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 234 277 (accept_3_3 17 234 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 234 277 (Polychromatic418967fa.accept_15_1_9_7_1_3130 16 234 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 234 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 234 277 (accept_3_3 14 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 234 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 234 277 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 234 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 277 (accept_3_3 11 234 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 277 (Polychromatic418967fa.accept_17_10_13_5_1_3513 10 234
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 234 277
  (Polychromatic418967fa.accept_17_9_13_5_1_3512 9 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 234 277 (accept_3_3 8 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  234 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 234 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 234 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 234 277 (accept_3_3 5 234 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 234 277 (Polychromatic418967fa.accept_22_4_14_13_1_5977 4 234 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 234 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 234 277 (accept_3_3 2 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  234 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 234 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 234 277)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 233 277 (Eq.refl Bool.true)
  (allA_of_3_1 45 233 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 232 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 232 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 232 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 232 277 (accept_3_3 44 232 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 232 277 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 232 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 232 277
  (Polychromatic418967fa.accept_20_2_12_17_1_5547 42 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 232 277 (accept_3_3 41 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 232 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 232 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 232 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 232 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 232 277 (accept_3_3 38 232 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 232 277
  (Polychromatic418967fa.accept_18_1_16_7_1_2897 37 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 232 277 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 232 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 232 277 (accept_3_3 35 232 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 232 277 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 232 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 232 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 232 277 (accept_3_3 32 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 232 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 232 277 (Polychromatic418967fa.accept_23_7_2_1_1_17037 30 232 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 232 277 (accept_3_3 29 232 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 232 277 (Polychromatic418967fa.accept_13_2_11_4_1_445 28 232
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 232 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 232 277 (accept_3_3 26 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 232 277 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 232 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 232 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 232 277 (accept_3_3 23 232 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 232 277 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 232 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 232 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 232 277 (accept_3_3 20 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 232 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 232 277 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 232 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 232 277 (accept_3_3 17 232 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 232 277 (Polychromatic418967fa.accept_17_16_11_5_1_9843 16 232
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 232 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 232 277 (accept_3_3 14 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 232 277 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 232 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 232 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 232 277 (accept_3_3 11 232 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 232 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 232 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 232 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 232 277 (accept_3_3 8 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  232 277 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 232 277 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 232 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 232 277 (accept_3_3 5 232 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 232 277 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 232 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 232 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 232 277 (accept_3_3 2 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  232 277 (Polychromatic418967fa.accept_18_1_16_7_1_2897 1 232 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 232 277)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 231 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 231 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 231 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 231 277 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 231
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 231 277 (accept_3_3 44 231
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 231 277
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 43 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 231 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 231 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 231 277 (accept_3_3 41 231 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 231 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 231 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 231 277 (Polychromatic418967fa.accept_9_3_6_7_1_562
  39 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 231 277 (accept_3_3 38
  231 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 231 277
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 231 277 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 231 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 231 277 (accept_3_3 35 231 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 231 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 231 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 231 277 (Polychromatic418967fa.accept_12_9_3_1_1_303
  33 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 231 277 (accept_3_3 32
  231 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 231 277
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 231 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 231 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 231 277 (accept_3_3 29 231 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 231 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 231 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 231 277 (Polychromatic418967fa.accept_13_1_10_4_1_954
  27 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 231 277 (accept_3_3 26
  231 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 231 277
  (Polychromatic418967fa.accept_20_5_11_17_1_5466 25 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 231 277 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 231 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 231 277 (accept_3_3 23 231 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 231 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 231 277 (accept_3_3 20 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 231 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 231 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 231 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 231 277 (accept_3_3 17 231 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 231 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 277
  (Polychromatic418967fa.accept_17_15_10_5_1_1573 15 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 231 277 (accept_3_3 14 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 231 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 231 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 231 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 277 (accept_3_3 11 231 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 231 277 (accept_3_3 8 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  231 277 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 231 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 231 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 277 (accept_3_3 5 231 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 231 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 231 277 (accept_3_3 2 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  231 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 231 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 231 277))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 230 277 (Eq.refl
  Bool.true) (allA_of_3_1 48 230 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 229 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 229 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 229 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 229 277 (accept_3_3 47 229 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 229 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 229 277
  (Polychromatic418967fa.accept_22_1_9_13_1_2894 45 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 229 277 (accept_3_3 44 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 229 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 229 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 229 277 (accept_3_3 41 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 229 277 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 229 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 229 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 229 277 (accept_3_3 38 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 229 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 229 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 229 277 (accept_3_3 35 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 229 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 229 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 229 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 229 277 (accept_3_3 32 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 229 277 (Polychromatic418967fa.accept_19_12_1_11_1_7538 31 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 229 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 229 277 (accept_3_3 29 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 229 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 229 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 229 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 229 277 (accept_3_3 26 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 229 277 (Polychromatic418967fa.accept_13_12_8_4_1_3099 25 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 229 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 229 277 (accept_3_3 23 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 229 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 229 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 229 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 229 277 (accept_3_3 20 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 229 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 229 277 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 229 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 229 277 (accept_3_3 17 229 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 229 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 229 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 229 277
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 229 277 (accept_3_3 14 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 229 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 229 277 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 277 (accept_3_3 11 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 229 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 277
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 229 277 (accept_3_3 8 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  229 277 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 229 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 277 (accept_3_3 5 229 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 277 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 229 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 277 (accept_3_3 2 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 229 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 277))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 228 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 228 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 228 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 228 277 (Polychromatic418967fa.accept_13_9_7_4_1_953
  48 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 228 277 (accept_3_3 47
  228 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 228 277
  (Polychromatic418967fa.accept_9_1_3_7_1_6 46 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 228 277 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 228 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 228 277 (accept_3_3 44 228 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 228 277 (Polychromatic418967fa.accept_14_1_4_11_1_3036 43 228 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 228 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 228 277 (accept_3_3 41 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 228 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 228 277 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 228 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 228 277 (accept_3_3 38 228 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 228 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 228 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 228 277
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 228 277 (accept_3_3 35 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 228 277 (Polychromatic418967fa.accept_15_4_3_7_1_713 34 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 228 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 228 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 228 277 (accept_3_3 32 228 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 228 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 228 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 228 277
  (Polychromatic418967fa.accept_20_10_8_17_1_12900 30 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 228 277 (accept_3_3 29 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 228 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 228 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 228 277 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 228
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 228 277 (accept_3_3 26 228
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 228 277
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 228 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 228 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 228 277 (accept_3_3 23 228 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 228 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 228 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 228 277
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 21 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 228 277 (accept_3_3 20 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 228 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 228 277 (Polychromatic418967fa.accept_23_18_21_1_1_15506 18 228 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 228 277 (accept_3_3 17 228 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 277 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 228
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 228 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 228 277 (accept_3_3 14 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 228 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 228 277 (Polychromatic418967fa.accept_13_12_7_4_1_3124 12 228 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 228 277 (accept_3_3 11 228 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 228 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 228 277
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 228 277 (accept_3_3 8 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  228 277 (Polychromatic418967fa.accept_14_7_4_11_1_3038 7 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 228 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 228 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 228 277 (accept_3_3 5 228 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 228 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 228 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 228 277
  (Polychromatic418967fa.accept_13_3_7_4_1_435 3 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 228 277 (accept_3_3 2 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  228 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 228 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 228 277)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 227 277 (Eq.refl
  Bool.true) (allA_of_3_1 51 227 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 226 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 226 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 226 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 226 277 (accept_3_3 50 226 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 226 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 226 277 (Polychromatic418967fa.accept_7_6_2_4_1_291
  48 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 226 277 (accept_3_3 47
  226 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 226 277
  (Polychromatic418967fa.accept_19_8_17_11_1_3406 46 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 226 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 226 277 (accept_3_3 44 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 226 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 226 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 226 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 226 277 (accept_3_3 41 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 226 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 226 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 226 277 (accept_3_3 38 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 226 277 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 226 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 226 277
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 226 277 (accept_3_3 35 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 226 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 226 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 226 277 (accept_3_3 32 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 226 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 226 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 226 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 226 277 (accept_3_3 29 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 226 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 226 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 226 277 (accept_3_3 26 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 226 277 (Polychromatic418967fa.accept_13_12_5_4_1_3133 25 226 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 226 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 226 277 (accept_3_3 23 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 226 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 226 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 226 277 (accept_3_3 20 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 226 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 226 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 226 277
  (Polychromatic418967fa.accept_19_18_17_11_1_9064 18 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 226 277 (accept_3_3 17 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 226 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 226 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 226 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 226 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 226 277 (accept_3_3 14 226 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 226 277 (Polychromatic418967fa.accept_7_6_2_4_1_291
  13 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 226 277
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 226 277 (accept_3_3 11 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 226 277 (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 226 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 226 277 (accept_3_3 8 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 226 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 226 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 226 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 226 277 (accept_3_3 5 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  226 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 226 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 226 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 277 (accept_3_3 2 226 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 226 277 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 226 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226
  277)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 225 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 225 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 225 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 225 277 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 225
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 225 277 (accept_3_3 50 225
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 225 277
  (Polychromatic418967fa.accept_24_1_9_13_1_13713 49 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 225 277 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 225 277 (accept_3_3 47 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 225 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 225 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 225 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 225 277 (accept_3_3 44 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 225 277 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 225 277 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 225 277 (accept_3_3 41 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 225 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 225 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 225 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 225 277 (accept_3_3 38 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 225 277 (Polychromatic418967fa.accept_27_10_9_7_1_13254 37 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 225 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 225 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 225 277 (accept_3_3 35 225 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 225 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 277
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 225 277 (accept_3_3 32 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 225 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 225 277 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 225 277 (accept_3_3 29 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 225 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 225 277 (accept_3_3 26 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 225 277 (Polychromatic418967fa.accept_16_9_1_5_1_2282 25 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 225 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 225 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 277 (accept_3_3 23 225 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 277
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 21 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 225 277 (accept_3_3 20 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 225 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 225 277 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 277 (accept_3_3 17 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 225 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 225 277 (accept_3_3 14 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 225 277 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 225 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 225 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 277 (accept_3_3 11 225 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 277
  (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 225 277 (accept_3_3 8 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  225 277 (Polychromatic418967fa.accept_29_7_22_16_1_17036 7 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 225 277 (Polychromatic418967fa.accept_16_6_1_5_1_2242 6 225 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 277 (accept_3_3 5 225 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 225 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 225 277 (accept_3_3 2 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  225 277 (Polychromatic418967fa.accept_17_1_4_5_1_3501 1 225 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 225 277))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 224 277 (Eq.refl
  Bool.true) (allA_of_3_1 54 224 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 223 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 223 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 223 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 223 277 (accept_3_3 53 223 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 223 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 223 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 51
  223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 223 277 (accept_3_3 50
  223 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 223 277
  (Polychromatic418967fa.accept_16_1_15_5_1_708 49 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 223 277 (Polychromatic418967fa.accept_17_14_2_5_1_3560 48 223 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 223 277 (accept_3_3 47 223 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 223 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 223 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 45
  223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 223 277 (accept_3_3 44
  223 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 223 277
  (Polychromatic418967fa.accept_19_5_14_11_1_6084 43 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 223 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 223 277 (accept_3_3 41 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 223 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 223 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 223 277
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 39 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 223 277 (accept_3_3 38 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 223 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 223 277 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 223 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 223 277 (accept_3_3 35 223 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 223 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 223 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 223 277
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 223 277 (accept_3_3 32 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 223 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 223 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 277 (accept_3_3 29 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 223 277 (Polychromatic418967fa.accept_19_9_14_11_1_7496 28 223 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 277
  (Polychromatic418967fa.accept_21_6_13_4_1_6521 27 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 223 277 (accept_3_3 26 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 223 277 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 223 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 277 (accept_3_3 23 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 223 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 277
  (Polychromatic418967fa.accept_15_6_13_7_1_222 21 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 223 277 (accept_3_3 20 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 223 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 223 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 277 (accept_3_3 17 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 223 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 277
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 277 (accept_3_3 14 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 277 (Polychromatic418967fa.accept_25_13_23_2_1_17035 13 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 223 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 277 (accept_3_3 11 223 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 223 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 277
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 223 277 (accept_3_3 8 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  223 277 (Polychromatic418967fa.accept_19_7_14_11_1_4724 7 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 223 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 277 (accept_3_3 5 223 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 277 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 223 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 277
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 277 (accept_3_3 2 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 277 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 223 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 277))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 222 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 55 222 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 222 277 (Polychromatic418967fa.accept_10_4_2_7_1_373
  54 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 222 277 (accept_3_3 53
  222 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 222 277
  (Polychromatic418967fa.accept_20_12_2_17_1_1620 52 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 222 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 222 277 (accept_3_3 50 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 222 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 222 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 222 277 (accept_3_3 47 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 222 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 222 277 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 222 277 (accept_3_3 44 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 222 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 222 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 222 277
  (Polychromatic418967fa.accept_13_3_1_4_1_945 42 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 222 277 (accept_3_3 41 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 222 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 222 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 222 277 (accept_3_3 38 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 222 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 222 277
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 222 277 (accept_3_3 35 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 222 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 222 277 (Polychromatic418967fa.accept_15_3_12_7_1_1346 33 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 222 277 (accept_3_3 32 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 222 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 222 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 222 277
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 222 277 (accept_3_3 29 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 222 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 222 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 222 277 (accept_3_3 26 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 222 277 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 222 277
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 222 277 (accept_3_3 23 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 222 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 222 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 222 277 (accept_3_3 20 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 222 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 222 277
  (Polychromatic418967fa.accept_13_5_1_4_1_3966 18 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 222 277 (accept_3_3 17 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 222 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 222 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 222 277 (accept_3_3 14 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 222 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 222 277 (accept_3_3 11 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 222 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 222 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 277 (accept_3_3 8 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 222 277 (accept_3_3 5 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  222 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 222 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 222 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 277 (accept_3_3 2 222 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 222 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  277)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 221 277 (Eq.refl Bool.true) (allA_of_3_1 57
  221 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 220 277 (Eq.refl Bool.true) (allA_succ_of_accept 57
  220 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 220 277 (accept_3_3 56 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 220 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 220 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 220 277 (Polychromatic418967fa.accept_13_2_12_4_1_943 54 220
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 220 277 (accept_3_3 53 220
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 220 277
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 52 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 220 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 220 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 220 277 (accept_3_3 50 220 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 220 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 220 277 (Polychromatic418967fa.accept_7_6_3_4_1_294
  48 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 220 277 (accept_3_3 47
  220 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 220 277
  (Polychromatic418967fa.accept_9_1_4_7_1_7 46 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 220 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 220 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 220 277 (accept_3_3 44 220 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 220 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 220 277 (Polychromatic418967fa.accept_9_6_4_7_1_300
  42 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 220 277 (accept_3_3 41
  220 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 220 277
  (Polychromatic418967fa.accept_16_8_12_5_1_200 40 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 220 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 220 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 220 277 (accept_3_3 38 220 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 220 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 220 277 (Polychromatic418967fa.accept_7_1_3_4_1_128
  36 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 220 277 (accept_3_3 35
  220 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 220 277
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 220 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 220 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 220 277 (accept_3_3 32 220 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 220 277 (Polychromatic418967fa.accept_13_5_12_4_1_449 31 220 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 220 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 220 277 (accept_3_3 29 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 220 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 220 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 220 277 (accept_3_3 26 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 220 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 220 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 220 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 220 277 (accept_3_3 23 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 220 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 220 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 220 277 (accept_3_3 20 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 220 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 220 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 220 277
  (Polychromatic418967fa.accept_13_5_12_4_1_449 18 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 220 277 (accept_3_3 17 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 220 277 (Polychromatic418967fa.accept_13_3_12_4_1_110 16 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 220 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 220 277 (accept_3_3 14 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 220 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 220 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 220 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 220 277 (accept_3_3 11 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 220 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 220 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 220 277 (accept_3_3 8 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 220 277 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 220 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 220 277
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 220 277 (accept_3_3 5 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  220 277 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 220 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 220 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 220 277 (accept_3_3 2 220 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 220 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 220 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220
  277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 219 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 219 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 219 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 219 277 (Polychromatic418967fa.accept_12_9_3_1_1_303 57 219
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 219 277 (accept_3_3 56 219
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 219 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 219 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 219 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 219 277 (accept_3_3 53 219 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 219 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 219 277 (Polychromatic418967fa.accept_9_6_3_7_1_580
  51 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 219 277 (accept_3_3 50
  219 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 219 277
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 219 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 219 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 219 277 (accept_3_3 47 219 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 219 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 219 277 (Polychromatic418967fa.accept_11_1_10_2_1_58
  45 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 219 277 (accept_3_3 44
  219 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 277
  (Polychromatic418967fa.accept_15_13_9_7_1_2194 43 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 219 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 219 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 219 277 (accept_3_3 41 219 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 219 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 219 277
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 39 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 219 277 (accept_3_3 38 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 219 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 219 277 (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 219 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 219 277 (accept_3_3 35 219 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 219 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 219 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 277
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 219 277 (accept_3_3 32 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 219 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 219 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 219 277 (accept_3_3 29 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 219 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 219 277 (accept_3_3 26 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 219 277 (Polychromatic418967fa.accept_13_12_11_4_1_3111 25 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 219 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 277 (accept_3_3 23 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 219 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 219 277 (accept_3_3 20 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 219 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 219 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 277 (accept_3_3 17 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 219 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 219 277 (accept_3_3 14 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 219 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 219 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 277 (accept_3_3 11 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 219 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 219 277 (accept_3_3 8 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  219 277 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 219 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 277 (accept_3_3 5 219 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 219 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 277
  (Polychromatic418967fa.accept_19_3_10_11_1_7669 3 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 219 277 (accept_3_3 2 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  219 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 219 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 219 277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 218 277
  (Eq.refl Bool.true) (allA_of_3_1 60 218 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 217 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 60 217 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 217 277 (accept_3_3 59 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 217 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 217 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 217 277 (accept_3_3 56 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 217 277 (Polychromatic418967fa.accept_19_17_8_11_1_7605 55 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 217 277 (Polychromatic418967fa.accept_19_16_8_11_1_6080 54 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 217 277 (accept_3_3 53 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 217 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 217 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 217 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 217 277 (accept_3_3 50 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 217 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 217 277 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 217 277 (accept_3_3 47 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 217 277 (Polychromatic418967fa.accept_13_7_9_4_1_918 46 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 217 277
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 217 277 (accept_3_3 44 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 217 277 (Polychromatic418967fa.accept_16_11_9_5_1_4412 43 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 217 277 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 217 277 (accept_3_3 41 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 217 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 217 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 217 277 (accept_3_3 38 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 217 277 (Polychromatic418967fa.accept_19_18_8_11_1_7663 37 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 217 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 217 277 (accept_3_3 35 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 217 277 (Polychromatic418967fa.accept_13_8_9_4_1_1552 34 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 217 277 (accept_3_3 32 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 217 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 217 277 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 277 (accept_3_3 29 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 217 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 217 277
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 217 277 (accept_3_3 26 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 217 277 (Polychromatic418967fa.accept_17_8_13_5_1_1597 25 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 217 277 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 277 (accept_3_3 23 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 217 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 217 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 217 277 (accept_3_3 20 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 217 277 (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 217 277 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 277 (accept_3_3 17 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 277 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 217
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 217 277 (accept_3_3 14 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 217 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 217 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 277 (accept_3_3 11 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 277 (Polychromatic418967fa.accept_14_10_7_11_1_3015 10 217 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 277
  (Polychromatic418967fa.accept_17_9_13_5_1_3512 9 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 277 (accept_3_3 8 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 277 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 277 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 277 (accept_3_3 5 217 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 217 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 277 (accept_3_3 2 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 277 (Polychromatic418967fa.accept_16_1_9_5_1_5443 1 217 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 216 277
  (Eq.refl Bool.true) (allA_succ_of_accept 61 216 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 216 277
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 60 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 216 277 (accept_3_3 59 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 216 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 216 277 (Polychromatic418967fa.accept_15_12_6_7_1_1353 57 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 216 277 (accept_3_3 56 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 216 277 (Polychromatic418967fa.accept_21_13_6_4_1_2178 55 216
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 216 277
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 216 277 (accept_3_3 53 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 216 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 216 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 216 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 216 277 (accept_3_3 50 216 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 216 277 (Polychromatic418967fa.accept_13_10_8_4_1_3098 49 216 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 216 277
  (Polychromatic418967fa.accept_13_9_8_4_1_937 48 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 216 277 (accept_3_3 47 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 216 277 (Polychromatic418967fa.accept_15_1_6_7_1_6282 46 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 216 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 216 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 216 277 (accept_3_3 44 216 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 216 277 (Polychromatic418967fa.accept_10_3_6_7_1_2188 43 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 216 277
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 216 277 (accept_3_3 41 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 216 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 216 277 (Polychromatic418967fa.accept_20_19_16_17_1_5473 39 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 216 277 (accept_3_3 38 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 216 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 216 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 216 277
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 216 277 (accept_3_3 35 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 216 277 (Polychromatic418967fa.accept_19_15_7_11_1_7657 34 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 216 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 216 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 216 277 (accept_3_3 32 216 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 216 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 216 277
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 216 277 (accept_3_3 29 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 216 277 (Polychromatic418967fa.accept_15_13_6_7_1_1369 28 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 216 277 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 216 277 (accept_3_3 26 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 216 277 (Polychromatic418967fa.accept_13_12_8_4_1_3099 25 216
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 216 277
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 216 277 (accept_3_3 23 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 216 277 (Polychromatic418967fa.accept_13_9_8_4_1_937 22 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 216 277 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 216 277 (accept_3_3 20 216 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 216 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 216 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 216 277
  (Polychromatic418967fa.accept_19_18_7_11_1_7552 18 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 216 277 (accept_3_3 17 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 216 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 216 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 216 277 (Polychromatic418967fa.accept_19_15_7_11_1_7657 15 216
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 277 (accept_3_3 14 216
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 277
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 216 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 216 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 216 277 (accept_3_3 11 216 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 216 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 216 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 216 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 9
  216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 216 277 (accept_3_3 8 216
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 277
  (Polychromatic418967fa.accept_17_7_12_5_1_1580 7 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 216 277 (Polychromatic418967fa.accept_20_6_16_17_1_5518 6 216 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 277 (accept_3_3 5 216 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 216 277 (Polychromatic418967fa.accept_16_4_8_5_1_3317 4 216 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 216 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 3
  216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 277 (accept_3_3 2 216
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 277
  (Polychromatic418967fa.accept_10_1_6_7_1_710 1 216 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 216 277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 215 277 (Eq.refl
  Bool.true) (allA_of_3_1 63 215 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 214 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 214 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 214 277 (accept_3_3 62 214 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 214 277 (Polychromatic418967fa.accept_10_1_4_7_1_374 61 214 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 214 277
  (Polychromatic418967fa.accept_28_4_18_25_1_17034 60 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 214 277 (accept_3_3 59 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 214 277 (Polychromatic418967fa.accept_18_4_16_7_1_1873 58 214 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 214 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 214 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 214 277 (accept_3_3 56 214 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 55
  214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 214 277
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 214 277 (accept_3_3 53 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 214 277 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 214 277 (accept_3_3 50 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 214 277 (Polychromatic418967fa.accept_13_10_6_4_1_1583 49 214 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 214 277
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 48 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 214 277 (accept_3_3 47 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 214 277 (Polychromatic418967fa.accept_13_7_6_4_1_933 46 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 214 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 214 277 (accept_3_3 44 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 214 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 214 277
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 214 277 (accept_3_3 41 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 214 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 214 277 (accept_3_3 38 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 214 277 (Polychromatic418967fa.accept_13_11_6_4_1_3121 37 214 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 214 277
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 214 277 (accept_3_3 35 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 214 277 (Polychromatic418967fa.accept_19_15_5_11_1_4719 34 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 214 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 214 277 (accept_3_3 32 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 214 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 214 277
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 214 277 (accept_3_3 29 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 214 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 214 277 (accept_3_3 26 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 214 277 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 214 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 214 277
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 214 277 (accept_3_3 23 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 214 277 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 214 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 214 277 (accept_3_3 20 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 214 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 214 277
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 214 277 (accept_3_3 17 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 214 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 214 277 (accept_3_3 14 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 214 277 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 214 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 214 277
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 214 277 (accept_3_3 11 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 214 277 (Polychromatic418967fa.accept_13_10_6_4_1_1583 10 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 214 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 214 277 (accept_3_3 8 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 214 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 214 277
  (Polychromatic418967fa.accept_19_6_5_11_1_6067 6 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 214 277 (accept_3_3 5 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  214 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 214 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 214 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 214 277 (accept_3_3 2 214 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 214 277 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 214 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 214
  277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 213 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 213 277 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 213
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 213 277 (accept_3_3 62 213
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 213 277
  (Polychromatic418967fa.accept_11_6_4_2_1_599 61 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 213 277 (Polychromatic418967fa.accept_19_3_4_11_1_469 60 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 213 277 (accept_3_3 59 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 213 277 (Polychromatic418967fa.accept_7_1_3_4_1_128
  57 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 213 277 (accept_3_3 56
  213 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 277
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 213 277 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 213 277 (accept_3_3 53 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 213 277 (Polychromatic418967fa.accept_12_3_9_1_1_290
  51 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 213 277 (accept_3_3 50
  213 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 277
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 213 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 213 277 (accept_3_3 47 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 213 277 (Polychromatic418967fa.accept_10_5_3_7_1_1108
  45 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 213 277 (accept_3_3 44
  213 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 277
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 213 277 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 277 (accept_3_3 41 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 213 277 (Polychromatic418967fa.accept_9_3_6_7_1_562
  39 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 277 (accept_3_3 38
  213 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 277
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 213 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 277 (accept_3_3 35 213 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 213 277
  (Polychromatic418967fa.accept_21_12_3_4_1_4988 33 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 213 277 (accept_3_3 32 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 213 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 213 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 277 (accept_3_3 29 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 213 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 213 277
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 213 277 (accept_3_3 26 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 213 277 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 213 277 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 213 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 277 (accept_3_3 23 213 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 213 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 213 277 (accept_3_3 20 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 213 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 213 277 (Polychromatic418967fa.accept_19_18_4_11_1_11751 18 213 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 277 (accept_3_3 17 213 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 213 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 277
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 213 277 (accept_3_3 14 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 213 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 213 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 277 (accept_3_3 11 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 213 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 277
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 213 277 (accept_3_3 8 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  213 277 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 213 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 277 (accept_3_3 5 213 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 213 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 213 277 (accept_3_3 2 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  213 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 213 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 213 277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 212 277
  (Eq.refl Bool.true) (allA_of_3_1 66 212 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 211 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 66 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 211 277 (accept_3_3 65 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 211 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 211 277
  (Polychromatic418967fa.accept_17_12_7_5_1_8659 63 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 211 277 (accept_3_3 62 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 211 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 211 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 211 277 (accept_3_3 59 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 211 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 211 277 (accept_3_3 56 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 211 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 211 277 (accept_3_3 53 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 211 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 211 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 51 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 211 277 (accept_3_3 50 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 211 277 (Polychromatic418967fa.accept_17_15_7_5_1_9836 49 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 211 277 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 211 277 (accept_3_3 47 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 211 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 211 277 (accept_3_3 44 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 211 277 (Polychromatic418967fa.accept_17_9_7_5_1_1566 43 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 211 277 (accept_3_3 41 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 211 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 211 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 211 277 (accept_3_3 38 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 211 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 211 277 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 211 277 (accept_3_3 35 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 211 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 211 277
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 211 277 (accept_3_3 32 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 211 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 211 277 (accept_3_3 29 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 211 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 277
  (Polychromatic418967fa.accept_13_1_3_4_1_925 27 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 211 277 (accept_3_3 26 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 211 277 (Polychromatic418967fa.accept_13_12_3_4_1_928 25 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 211 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 277 (accept_3_3 23 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 277 (accept_3_3 20 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 277 (accept_3_3 17 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 277 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 277 (accept_3_3 14 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 277 (Polychromatic418967fa.accept_19_13_2_11_1_9083 13 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 277 (accept_3_3 11 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 277
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 277 (accept_3_3 8 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 277 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 277 (accept_3_3 5 211 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 277 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 211 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 277 (accept_3_3 2 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 211 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 210
  277 (Eq.refl Bool.true) (allA_succ_of_accept 67 210 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 210 277
  (Polychromatic418967fa.accept_19_9_1_11_1_7643 66 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 210 277 (accept_3_3 65 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 210 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 210 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 210 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 210 277 (accept_3_3 62 210 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 210 277 (Polychromatic418967fa.accept_16_13_2_5_1_3336 61 210 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 210 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 210 277 (accept_3_3 59 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 210 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 210 277 (Polychromatic418967fa.accept_13_5_2_4_1_3955 57 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 210 277 (accept_3_3 56 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 210 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 210 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 210 277
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 210 277 (accept_3_3 53 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 210 277 (Polychromatic418967fa.accept_17_1_6_5_1_3502 52 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 210 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 210 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 210 277 (accept_3_3 50 210 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 210 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 210 277
  (Polychromatic418967fa.accept_19_10_1_11_1_7532 48 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 210 277 (accept_3_3 47 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 210 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 210 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 210 277 (Polychromatic418967fa.accept_13_6_2_4_1_923 45 210
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 210 277 (accept_3_3 44 210
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 210 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 210 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 210 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 210 277 (accept_3_3 41 210 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 210 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 210 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 210 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 210 277 (accept_3_3 38
  210 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 210 277
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 210 277 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 210 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 210 277 (accept_3_3 35 210 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 210 277 (Polychromatic418967fa.accept_19_15_1_11_1_7503 34 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 210 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 210 277 (accept_3_3 32 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 210 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 210 277 (Polychromatic418967fa.accept_24_6_18_13_1_15468 30 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 210 277 (accept_3_3 29 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 210 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 210 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 210 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 210 277 (accept_3_3 26 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 210 277 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 210 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 210 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 210 277 (accept_3_3 23 210 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 210 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 210 277
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 210 277 (accept_3_3 20 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 210 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 210 277 (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 210 277 (accept_3_3 17 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 277 (Polychromatic418967fa.accept_25_16_10_2_1_11779 16
  210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 210 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 210 277 (accept_3_3 14 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 210 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 210 277 (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 210 277 (accept_3_3 11 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 210 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 210 277
  (Polychromatic418967fa.accept_19_9_1_11_1_7643 9 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 210 277 (accept_3_3 8 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  210 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 210 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 210 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 210 277 (accept_3_3 5 210 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 210 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 210 277 (accept_3_3 2 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  210 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 210 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 210 277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 209
  277 (Eq.refl Bool.true) (allA_of_3_1 69 209 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 208 277
  (Eq.refl Bool.true) (allA_succ_of_accept 69 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 208 277 (accept_3_3 68 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 208 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 208 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 208 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 208 277 (accept_3_3 65 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 208 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 208 277 (accept_3_3 62 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 208 277 (Polychromatic418967fa.accept_19_4_18_11_1_7528 61 208 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 208 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 208 277 (accept_3_3 59 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 208 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 208 277 (accept_3_3 56 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 208 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 208 277
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 54 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 208 277 (accept_3_3 53 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 208 277 (Polychromatic418967fa.accept_17_1_4_5_1_3501 52 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 208 277 (accept_3_3 50 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 208 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 208 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 208 277 (accept_3_3 47 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 208 277 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 208 277 (accept_3_3 44 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 208 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 208 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 208 277 (accept_3_3 41 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 208 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 208 277 (accept_3_3 38 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 208 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 208 277
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 208 277 (accept_3_3 35 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 208 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 208 277 (accept_3_3 32 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 208 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 208 277
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 208 277 (accept_3_3 29 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 208 277 (Polychromatic418967fa.accept_21_7_19_4_1_4956 28 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 208 277 (accept_3_3 26 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 208 277 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 208 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 208 277 (accept_3_3 23 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 208 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 208 277 (accept_3_3 20 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 208 277 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 208 277
  (Polychromatic418967fa.accept_17_1_4_5_1_3501 18 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 208 277 (accept_3_3 17 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 208 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 208 277 (accept_3_3 14 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 208 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 208 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 208 277 (accept_3_3 11 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 208 277 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 208 277 (accept_3_3 8 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 208 277 (Polychromatic418967fa.accept_19_7_18_11_1_464 7 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 208 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 208 277 (accept_3_3 5 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  208 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 208 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 208 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 277 (accept_3_3 2 208 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 208 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 208 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208
  277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 207 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 207 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 207 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 207 277 (Polychromatic418967fa.accept_12_9_3_1_1_303 69 207
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 207 277 (accept_3_3 68 207
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 207 277
  (Polychromatic418967fa.accept_13_2_12_4_1_943 67 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 207 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 207 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 207 277 (accept_3_3 65 207 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 207 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 207 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 207 277
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 63 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 207 277 (accept_3_3 62 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 207 277 (Polychromatic418967fa.accept_19_4_17_11_1_7527 61 207 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 207 277
  (Polychromatic418967fa.accept_13_8_12_4_1_4858 60 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 207 277 (accept_3_3 59 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 207 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 207 277 (Polychromatic418967fa.accept_12_9_3_1_1_303 57 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 207 277 (accept_3_3 56 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 277 (Polychromatic418967fa.accept_13_3_12_4_1_110 55 207
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 207 277
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 207 277 (accept_3_3 53 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 207 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 207 277 (Polychromatic418967fa.accept_11_7_9_2_1_260 51 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 207 277 (accept_3_3 50 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 277 (Polychromatic418967fa.accept_15_4_12_7_1_3115 49 207
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 277
  (Polychromatic418967fa.accept_11_4_9_2_1_259 48 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 207 277 (accept_3_3 47 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 207 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 207 277 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 277 (accept_3_3 44 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 277 (Polychromatic418967fa.accept_19_5_17_11_1_2225 43 207
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 277
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 207 277 (accept_3_3 41 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 207 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 207 277 (Polychromatic418967fa.accept_18_3_9_7_1_1839 39 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 207 277 (accept_3_3 38 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 277 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 207
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 277
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 207 277 (accept_3_3 35 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 207 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 207 277 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 277 (accept_3_3 32 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 277 (Polychromatic418967fa.accept_13_5_12_4_1_449 31 207
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 277
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 207 277 (accept_3_3 29 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 207 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 207 277 (Polychromatic418967fa.accept_19_8_17_11_1_3406 27 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 277 (accept_3_3 26 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 277 (Polychromatic418967fa.accept_15_10_12_7_1_1358 25 207
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 277
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 207 277 (accept_3_3 23 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 207 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 277 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 207
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 277 (accept_3_3 20 207
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 277
  (Polychromatic418967fa.accept_15_4_12_7_1_3115 19 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 207 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 207 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 277 (accept_3_3 17 207 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 207 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 207 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 277 (Polychromatic418967fa.accept_11_4_9_2_1_259
  15 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 277 (accept_3_3 14
  207 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 277
  (Polychromatic418967fa.accept_19_13_17_11_1_4716 13 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 207 277 (Polychromatic418967fa.accept_20_12_7_17_1_12857 12 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 277 (accept_3_3 11 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 207 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 207 277 (accept_3_3 8 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  207 277 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 207 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 277 (accept_3_3 5 207 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 277
  (Polychromatic418967fa.accept_13_3_12_4_1_110 3 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 277 (accept_3_3 2 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  207 277 (Polychromatic418967fa.accept_16_1_15_5_1_708 1 207 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72
  206 277 (Eq.refl Bool.true) (allA_of_3_1 72 206 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 205 277
  (Eq.refl Bool.true) (allA_succ_of_accept 72 205 277 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 205 277 (accept_3_3 71 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 205 277 (Polychromatic418967fa.accept_13_5_10_4_1_1564 70 205
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 205 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 205 277 (accept_3_3 68 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 205 277 (Polychromatic418967fa.accept_17_16_1_5_1_2600 67 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 205 277 (Polychromatic418967fa.accept_13_1_10_4_1_954 66 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 205 277 (accept_3_3 65 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 205 277 (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 205
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 205 277
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 205 277 (accept_3_3 62 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 205 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 205 277 (Polychromatic418967fa.accept_13_8_10_4_1_2270 60 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 205 277 (accept_3_3 59 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 205 277 (Polychromatic418967fa.accept_10_8_5_7_1_358 58 205
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 205 277
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 57 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 205 277 (accept_3_3 56 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 205 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 205 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 205 277 (accept_3_3 53 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 205 277 (Polychromatic418967fa.accept_10_2_5_7_1_1124 52 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 205 277
  (Polychromatic418967fa.accept_20_11_5_17_1_5490 51 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 205 277 (accept_3_3 50 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 205 277 (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 205 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 205 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 205 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 277 (accept_3_3 47 205 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 277 (Polychromatic418967fa.accept_13_7_10_4_1_919
  46 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 205 277
  (Polychromatic418967fa.accept_13_6_10_4_1_957 45 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 205 277 (accept_3_3 44 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 205 277 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 205 277 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 277 (accept_3_3 41 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 205 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 205 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 205 277
  (Polychromatic418967fa.accept_19_1_15_11_1_4712 39 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 205 277 (accept_3_3 38 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 205 277 (Polychromatic418967fa.accept_13_11_10_4_1_1565 37 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 205 277
  (Polychromatic418967fa.accept_27_9_16_7_1_9526 36 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 205 277 (accept_3_3 35 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 205 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 205 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 277 (accept_3_3 32 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 205 277 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 205 277
  (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 205 277 (accept_3_3 29 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 205 277 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 205 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 277 (accept_3_3 26 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 277 (Polychromatic418967fa.accept_16_9_13_5_1_2238 25 205 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 277
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 24 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 205 277 (accept_3_3 23 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 205 277 (Polychromatic418967fa.accept_10_2_5_7_1_1124 22 205 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 277 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 205
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 277 (accept_3_3 20 205
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 277
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 205 277 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 205 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 277 (accept_3_3 17 205 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 205 277 (Polychromatic418967fa.accept_14_2_9_11_1_3054 16 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 277
  (Polychromatic418967fa.accept_20_15_5_17_1_5495 15 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 205 277 (accept_3_3 14 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 205 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 205 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 205 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 277 (accept_3_3 11 205 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 277
  (Polychromatic418967fa.accept_16_10_13_5_1_3292 10 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 205 277 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 277 (accept_3_3 8 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 277 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 277 (accept_3_3 5 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 277 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 205 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 277 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 277 (accept_3_3 2 205 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 277 (Polychromatic418967fa.accept_13_1_10_4_1_954 1 205 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205
  277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 204 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 204 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 204 277 (Polychromatic418967fa.accept_10_2_4_7_1_352
  72 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 204 277 (accept_3_3 71
  204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 204 277
  (Polychromatic418967fa.accept_11_4_6_2_1_51 70 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 204 277 (Polychromatic418967fa.accept_21_6_15_4_1_5021 69 204 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 204 277 (accept_3_3 68 204 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 204 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 204 277 (Polychromatic418967fa.accept_7_3_1_4_1_121
  66 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 204 277 (accept_3_3 65
  204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 204 277
  (Polychromatic418967fa.accept_9_1_6_7_1_285 64 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 204 277 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 204 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 204 277 (accept_3_3 62 204 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 204 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 204 277 (Polychromatic418967fa.accept_13_8_9_4_1_1552
  60 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 204 277 (accept_3_3 59
  204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 204 277
  (Polychromatic418967fa.accept_9_4_6_7_1_286 58 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 204 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 204 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 204 277 (accept_3_3 56 204 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 204 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 204 277 (Polychromatic418967fa.accept_7_5_1_4_1_122
  54 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 204 277 (accept_3_3 53
  204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 204 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 52 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 204 277 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 204 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 204 277 (accept_3_3 50 204 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 204 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 204 277 (Polychromatic418967fa.accept_9_3_6_7_1_562
  48 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 204 277 (accept_3_3 47
  204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 204 277
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 204 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 204 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 204 277 (accept_3_3 44 204 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 204 277 (Polychromatic418967fa.accept_10_3_4_7_1_353 43 204 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 204 277
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 204 277 (accept_3_3 41 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 204 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 204 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 204 277 (accept_3_3 38 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 204 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 204 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 204 277
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 36 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 204 277 (accept_3_3 35 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 204 277 (Polychromatic418967fa.accept_13_8_9_4_1_1552 34 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 204 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 204 277 (accept_3_3 32 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 204 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 204 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 204 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 204 277 (accept_3_3 29 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 204 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 204 277 (Polychromatic418967fa.accept_18_9_6_7_1_6719 27 204 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 277 (accept_3_3 26 204 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 204 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 204 277 (accept_3_3 23 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 204 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 204 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 277 (accept_3_3 20 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 204 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 277
  (Polychromatic418967fa.accept_13_5_9_4_1_441 18 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 204 277 (accept_3_3 17 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 204 277 (Polychromatic418967fa.accept_15_1_9_7_1_3130 16 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 204 277 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 277 (accept_3_3 14 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 204 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 277
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 204 277 (accept_3_3 11 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 204 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 204 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 277 (accept_3_3 8 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 277 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 204 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 277
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 6 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 204 277 (accept_3_3 5 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  204 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 204 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 204 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 277 (accept_3_3 2 204 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 204 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 203 277 (Eq.refl
  Bool.true) (allA_of_3_1 75 203 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 202 277 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 202 277 (accept_3_3 74 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 202 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 202 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 72
  202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 202 277 (accept_3_3 71
  202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 202 277
  (Polychromatic418967fa.accept_18_16_4_7_1_2927 70 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 202 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 202 277 (accept_3_3 68 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 202 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 66
  202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 202 277 (accept_3_3 65
  202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 202 277
  (Polychromatic418967fa.accept_9_1_4_7_1_7 64 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 202 277 (accept_3_3 62 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 202 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 202 277 (Polychromatic418967fa.accept_9_6_4_7_1_300
  60 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 202 277 (accept_3_3 59
  202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 202 277
  (Polychromatic418967fa.accept_7_2_6_4_1_29 58 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 202 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 202 277 (accept_3_3 56 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 202 277 (Polychromatic418967fa.accept_7_5_6_4_1_117
  54 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 202 277 (accept_3_3 53
  202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 202 277
  (Polychromatic418967fa.accept_7_3_6_4_1_30 52 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 202 277 (accept_3_3 50 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 202 277 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 202 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 202 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 202 277 (accept_3_3 47 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 202 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 202 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 202 277 (accept_3_3 44 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 202 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 202 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 202 277 (accept_3_3 41 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 202 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 202 277 (accept_3_3 38 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 202 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 202 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 202 277
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 202 277 (accept_3_3 35 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 202 277 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 202 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 202 277 (accept_3_3 32 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 202 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 202 277
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 202 277 (accept_3_3 29 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 202 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 202 277 (accept_3_3 26 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 202 277 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 202 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 202 277
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 202 277 (accept_3_3 23 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 202 277 (Polychromatic418967fa.accept_13_9_7_4_1_953 22 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 202 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 202 277 (accept_3_3 20 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 202 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 202 277
  (Polychromatic418967fa.accept_19_18_12_11_1_3386 18 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 202 277 (accept_3_3 17 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 202 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 202 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 202 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 202 277 (accept_3_3 14 202 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 202 277
  (Polychromatic418967fa.accept_16_13_10_5_1_2278 13 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 202 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 202 277 (accept_3_3 11 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 202 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 202 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 202 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 202 277 (accept_3_3 8 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  202 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 202 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 202 277 (accept_3_3 5 202 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 202 277 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 202 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 202 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 202 277 (accept_3_3 2 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  202 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 202 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 202 277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  77 201 277 (Eq.refl Bool.true) (allA_succ_of_accept 76 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 201 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 201 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 201 277 (accept_3_3 74 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 201 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 201 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 201 277 (accept_3_3 71 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 201 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 201 277 (accept_3_3 68 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 201 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 201 277 (Polychromatic418967fa.accept_10_6_1_7_1_342 66 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 201 277 (accept_3_3 65 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 201 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 201 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 201 277 (accept_3_3 62 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 201 277 (Polychromatic418967fa.accept_13_9_6_4_1_2243 61 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 201 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 201 277 (accept_3_3 59 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 201 277
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 201 277 (accept_3_3 56 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 201 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 201 277 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 201 277 (accept_3_3 53 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 201 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 201 277
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 201 277 (accept_3_3 50 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 201 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 201 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 201 277 (accept_3_3 47 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 201 277
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 201 277 (accept_3_3 44 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 201 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 201 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 201 277 (accept_3_3 41 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 201 277 (accept_3_3 38 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 201 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 201 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 277 (accept_3_3 35 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 201 277 (accept_3_3 32 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 201 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 201 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 277 (accept_3_3 29 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 201 277 (accept_3_3 26 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 201 277 (Polychromatic418967fa.accept_23_2_17_1_1_16972 25 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 201 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 277 (accept_3_3 23 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 201 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 277
  (Polychromatic418967fa.accept_25_21_1_2_1_17033 21 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 201 277 (accept_3_3 20 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 201 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 277 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 201
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 277 (accept_3_3 17 201
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 277
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 201 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 201 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 277 (accept_3_3 14 201 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 201 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 277 (Polychromatic418967fa.accept_8_4_1_5_1_186
  12 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 277 (accept_3_3 11
  201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 277
  (Polychromatic418967fa.accept_6_4_3_1_1_57 10 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 201 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 201 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 277 (accept_3_3 8 201 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 201 277 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 201 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 277 (accept_3_3 5 201
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 277 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 201 277 (accept_3_3 2 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  201 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 201 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 201 277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  78 200 277 (Eq.refl Bool.true) (allA_of_3_1 78 200 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 199 277
  (Eq.refl Bool.true) (allA_succ_of_accept 78 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 199 277 (accept_3_3 77 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 199 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 199 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 199 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 75 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 199 277 (accept_3_3 74 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 199 277 (Polychromatic418967fa.accept_24_1_7_13_1_11961 73 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 199 277 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 199 277 (accept_3_3 71 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 199 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 199 277
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 199 277 (accept_3_3 68 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 199 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 199 277 (accept_3_3 65 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 199 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 199 277
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 199 277 (accept_3_3 62 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 199 277 (Polychromatic418967fa.accept_17_10_12_5_1_6028 61 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 199 277 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 199 277 (accept_3_3 59 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 199 277
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 199 277 (accept_3_3 56 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 199 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 199 277 (accept_3_3 53 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 199 277 (Polychromatic418967fa.accept_10_2_9_7_1_720 52 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 199 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 199 277 (accept_3_3 50 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 199 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 199 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 199 277 (accept_3_3 47 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 199 277
  (Polychromatic418967fa.accept_19_7_9_11_1_7493 45 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 199 277 (accept_3_3 44 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 199 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 199 277 (accept_3_3 41 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 199 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 199 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 199 277 (accept_3_3 38 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 199 277 (Polychromatic418967fa.accept_21_16_10_4_1_3433 37 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 199 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 199 277 (accept_3_3 35 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 199 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 199 277 (accept_3_3 32 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 199 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 277 (accept_3_3 29 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 199 277 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 277
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 199 277 (accept_3_3 26 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 199 277 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 199 277 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 277 (accept_3_3 23 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 277 (accept_3_3 20 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 277 (Polychromatic418967fa.accept_21_19_10_4_1_14102 19 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 277 (accept_3_3 17 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 277 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 199
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 277
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 199 277 (accept_3_3 14 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 199 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 199 277 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 277 (accept_3_3 11 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 277
  (Polychromatic418967fa.accept_17_9_12_5_1_219 9 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 277 (accept_3_3 8 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 277 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 277 (accept_3_3 5 199 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 199 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 277 (accept_3_3 2 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 199 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 198 277 (Eq.refl Bool.true) (allA_succ_of_accept 79 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50
  79 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 198 277
  (Polychromatic418967fa.accept_19_2_8_11_1_7701 78 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 198 277 (accept_3_3 77 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 198 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 198 277 (accept_3_3 74 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 198 277 (Polychromatic418967fa.accept_19_16_8_11_1_6080 73 198 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 198 277
  (Polychromatic418967fa.accept_13_7_3_4_1_459 72 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 198 277 (accept_3_3 71 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 198 277 (Polychromatic418967fa.accept_15_10_3_7_1_715 70 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 198 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 198 277 (accept_3_3 68 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 198 277
  (Polychromatic418967fa.accept_13_1_3_4_1_925 66 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 198 277 (accept_3_3 65 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 198 277 (Polychromatic418967fa.accept_13_12_3_4_1_928 64 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 198 277 (accept_3_3 62 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 198 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 198 277
  (Polychromatic418967fa.accept_19_3_8_11_1_7609 60 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 198 277 (accept_3_3 59 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 198 277 (Polychromatic418967fa.accept_17_7_11_5_1_3539 58 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 198 277 (Polychromatic418967fa.accept_15_12_3_7_1_4123 57 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 198 277 (accept_3_3 56 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 198 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 198 277
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 198 277 (accept_3_3 53 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 198 277 (Polychromatic418967fa.accept_16_4_6_5_1_2245 52 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 198 277 (accept_3_3 50 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 198 277 (Polychromatic418967fa.accept_10_9_8_7_1_714 49 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 198 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 198 277 (accept_3_3 47 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 198 277 (Polychromatic418967fa.accept_13_7_3_4_1_459 46 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 198 277 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 198 277 (accept_3_3 44 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 198 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 198 277
  (Polychromatic418967fa.accept_15_12_3_7_1_4123 42 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 198 277 (accept_3_3 41 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 198 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 198 277 (accept_3_3 38 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 198 277 (Polychromatic418967fa.accept_14_9_2_11_1_780 37 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 198 277
  (Polychromatic418967fa.accept_16_4_6_5_1_2245 36 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 198 277 (accept_3_3 35 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 198 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 198 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 198 277 (accept_3_3 32 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 198 277
  (Polychromatic418967fa.accept_20_10_18_17_1_11453 30 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 198 277 (accept_3_3 29 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 198 277 (Polychromatic418967fa.accept_19_9_8_11_1_6072 28 198 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 198 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 277 (accept_3_3 26 198 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 277 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  25 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 277
  (Polychromatic418967fa.accept_17_7_11_5_1_3539 24 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 198 277 (accept_3_3 23 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 198 277 (Polychromatic418967fa.accept_19_3_8_11_1_7609 22 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 198 277 (Polychromatic418967fa.accept_19_2_8_11_1_7701 21 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 277 (accept_3_3 20 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 198 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 277
  (Polychromatic418967fa.accept_19_18_8_11_1_7663 18 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 198 277 (accept_3_3 17 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 198 277 (Polychromatic418967fa.accept_17_16_11_5_1_9843 16 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 277 (accept_3_3 14
  198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 198 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 198 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 198 277 (accept_3_3 11 198 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 198 277 (Polychromatic418967fa.accept_15_10_3_7_1_715 10 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 277
  (Polychromatic418967fa.accept_10_9_8_7_1_714 9 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 198 277 (accept_3_3 8 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  198 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 198 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 198 277 (accept_3_3 5 198 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 198 277 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 198 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 198 277
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 198 277 (accept_3_3 2 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  198 277 (Polychromatic418967fa.accept_13_1_3_4_1_925 1 198 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 198 277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 197 277 (Eq.refl Bool.true) (allA_of_3_1 81 197 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 82 196 277 (Eq.refl Bool.true) (allA_succ_of_accept 81 196 277 (Polychromatic418967fa.accept_6_3_4_1_1_8
  81 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 196 277 (accept_3_3 80
  196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 196 277
  (Polychromatic418967fa.accept_16_15_4_5_1_1411 79 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 196 277 (Polychromatic418967fa.accept_23_9_12_1_1_12155 78 196 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 196 277 (accept_3_3 77 196 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 196 277 (Polychromatic418967fa.accept_16_12_4_5_1_2273 76 196 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 196 277 (accept_3_3 74 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 196 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 196 277 (Polychromatic418967fa.accept_16_8_4_5_1_4379 72 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 196 277 (accept_3_3 71 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 196 277 (Polychromatic418967fa.accept_11_4_9_2_1_259 70 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 196 277 (accept_3_3 68 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 196 277 (Polychromatic418967fa.accept_20_7_16_17_1_9967 67 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 196 277 (Polychromatic418967fa.accept_15_6_1_7_1_4079 66 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 196 277 (accept_3_3 65 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 196 277 (Polychromatic418967fa.accept_17_13_9_5_1_6022 64 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 196 277 (accept_3_3 62 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 196 277 (Polychromatic418967fa.accept_10_1_6_7_1_710 61 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 196 277 (Polychromatic418967fa.accept_16_12_4_5_1_2273 60 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 196 277 (accept_3_3 59 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 196 277 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 196 277 (accept_3_3 56 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 196 277 (Polychromatic418967fa.accept_13_3_1_4_1_945 55 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 196 277 (Polychromatic418967fa.accept_15_9_1_7_1_1350 54 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 196 277 (accept_3_3 53 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 196 277 (Polychromatic418967fa.accept_19_14_6_11_1_7599 52 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 196 277 (accept_3_3 50 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 196 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 196 277 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 196 277 (accept_3_3 47 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 196 277 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 196 277 (accept_3_3 44 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 196 277 (Polychromatic418967fa.accept_10_3_6_7_1_2188 43 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 196 277 (Polychromatic418967fa.accept_13_3_1_4_1_945 42 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 196 277 (accept_3_3 41 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 196 277 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 196 277 (accept_3_3 38 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 196 277 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 196 277 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 196 277 (accept_3_3 35 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 196 277 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 196 277 (accept_3_3 32 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 196 277 (Polychromatic418967fa.accept_10_1_6_7_1_710 31 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 196 277 (Polychromatic418967fa.accept_17_13_9_5_1_6022 30 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 196 277 (accept_3_3 29 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 196 277 (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 196 277 (accept_3_3 26 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 196 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 196 277 (Polychromatic418967fa.accept_15_9_1_7_1_1350 24 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 196 277 (accept_3_3 23 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 196 277 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 196 277 (accept_3_3 20 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 196 277 (Polychromatic418967fa.accept_18_1_16_7_1_2897 19 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 196 277 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 196 277 (accept_3_3 17 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 196 277 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 196 277 (accept_3_3 14 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 196 277 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 196 277 (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 196 277 (accept_3_3 11 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 196 277 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 196
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 196 277 (accept_3_3 8 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  196 277 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 196 277 (Polychromatic418967fa.accept_15_6_1_7_1_4079 6 196 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 196 277 (accept_3_3 5 196 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 196 277 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 196 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 196 277
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 196 277 (accept_3_3 2 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  196 277 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 196 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 196 277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 195 277 (Eq.refl Bool.true) (allA_succ_of_accept 82 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2
  82 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 195 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 81 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 195 277 (accept_3_3 80 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 195 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 195 277 (accept_3_3 77 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 195 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 195 277
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 195 277 (accept_3_3 74 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 195 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 195 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 195 277 (accept_3_3 71 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 195 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 195 277 (accept_3_3 68 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 195 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 195 277 (accept_3_3 65 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 195 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 195 277
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 195 277 (accept_3_3 62 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 195 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 195 277 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 195 277 (accept_3_3 59 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 195 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 195 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 195 277 (accept_3_3 56 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 195 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 195 277 (accept_3_3 53 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 195 277
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 195 277 (accept_3_3 50 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 195 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 195 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 277 (accept_3_3 47 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 195 277
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 195 277 (accept_3_3 44 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 195 277 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 277 (accept_3_3 41 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 195 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 195 277 (accept_3_3 38 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 195 277 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 195 277 (Polychromatic418967fa.accept_19_17_5_11_1_7509 36 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 277 (accept_3_3 35 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 195 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 277
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 195 277 (accept_3_3 32 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 195 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 277 (accept_3_3 29 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 277
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 195 277 (accept_3_3 26 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 195 277 (Polychromatic418967fa.accept_19_6_5_11_1_6067 25 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 195 277 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 277 (accept_3_3 23 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 195 277 (accept_3_3 20 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 195 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 277 (accept_3_3 17 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 277
  (Polychromatic418967fa.accept_19_15_5_11_1_4719 15 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 277 (accept_3_3 14 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 195 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 195 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 277 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 195 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 277 (accept_3_3 11 195 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 277
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 277 (accept_3_3 8 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  195 277 (Polychromatic418967fa.accept_21_7_6_4_1_3445 7 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 277 (accept_3_3 5 195 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 195 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 277
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 277 (accept_3_3 2 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  195 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 195 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 84 194 277 (Eq.refl Bool.true) (allA_of_3_1 84 194 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 85 193 277 (Eq.refl Bool.true) (allA_succ_of_accept 84 193 277 (Polychromatic418967fa.accept_8_4_1_5_1_186
  84 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 193 277 (accept_3_3 83
  193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 193 277
  (Polychromatic418967fa.accept_9_1_4_7_1_7 82 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 193 277 (Polychromatic418967fa.accept_11_4_6_2_1_51 81 193 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 193 277 (accept_3_3 80 193 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 193 277 (Polychromatic418967fa.accept_16_15_1_5_1_2265 79 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 193 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 193 277 (accept_3_3 77 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 193 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 76 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 193 277 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 193 277 (accept_3_3 74 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 193 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 193 277
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 72 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 193 277 (accept_3_3 71 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 193 277 (Polychromatic418967fa.accept_11_4_6_2_1_51 70 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 193 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 193 277 (accept_3_3 68 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 193 277 (Polychromatic418967fa.accept_13_2_11_4_1_445 67 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 193 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 193 277 (accept_3_3 65 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 193 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 193 277 (Polychromatic418967fa.accept_16_15_1_5_1_2265 63 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 193 277 (accept_3_3 62 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 193 277 (Polychromatic418967fa.accept_16_13_1_5_1_5469 61 193
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 193 277
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 193 277 (accept_3_3 59 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 193 277 (Polychromatic418967fa.accept_13_6_11_4_1_938 58 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 193 277 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 193 277 (accept_3_3 56 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 193 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 193 277
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 193 277 (accept_3_3 53 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 193 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 193 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 277 (accept_3_3 50 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 193 277 (Polychromatic418967fa.accept_13_10_11_4_1_2248 49 193 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 193 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 193 277 (accept_3_3 47 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 193 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 193 277 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 277 (accept_3_3 44 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 277 (Polychromatic418967fa.accept_22_21_17_13_1_17032 43
  193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 277 (accept_3_3 41 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 277 (Polychromatic418967fa.accept_18_4_13_7_1_5395 40 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 193 277 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 277 (accept_3_3 38 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 277
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 277 (accept_3_3 35 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 277 (Polychromatic418967fa.accept_10_4_3_7_1_1110 34 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 193 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 277 (accept_3_3 32 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 277 (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 193 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 277 (accept_3_3 29 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 277 (Polychromatic418967fa.accept_19_8_3_11_1_6048 27 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 277 (accept_3_3 26 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 277 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 193
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 277 (accept_3_3 23 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 277 (Polychromatic418967fa.accept_16_6_1_5_1_2242 22 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 277 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 277 (accept_3_3 20 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 277
  (Polychromatic418967fa.accept_17_1_6_5_1_3502 18 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 277 (accept_3_3 17 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 277 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 277 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 277 (accept_3_3 14 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 277 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 193 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 277
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 277 (accept_3_3 11 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 277 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 277 (accept_3_3 8 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 277 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 193
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 277 (accept_3_3 5 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 277 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 193 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 277 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 277 (accept_3_3 2 193 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 193 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193
  277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 192 277
  (Eq.refl Bool.true) (allA_succ_of_accept 85 192 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 192 277
  (Polychromatic418967fa.accept_10_4_2_7_1_373 84 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 192 277 (accept_3_3 83 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 192 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 192 277 (Polychromatic418967fa.accept_15_6_12_7_1_1360 81 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 192 277 (accept_3_3 80 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 192 277 (Polychromatic418967fa.accept_10_9_2_7_1_1096 79 192
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 192 277
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 192 277 (accept_3_3 77 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 192 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 192 277 (Polychromatic418967fa.accept_10_5_2_7_1_345 75 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 192 277 (accept_3_3 74 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 192 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 192 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 192 277
  (Polychromatic418967fa.accept_13_7_10_4_1_919 72 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 192 277 (accept_3_3 71 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 192 277 (Polychromatic418967fa.accept_13_5_10_4_1_1564 70 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 192 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 192 277 (accept_3_3 68 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 192 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 192 277
  (Polychromatic418967fa.accept_13_1_10_4_1_954 66 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 192 277 (accept_3_3 65 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 192 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 192 277 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 192 277 (accept_3_3 62 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 192 277 (Polychromatic418967fa.accept_19_4_2_11_1_3409 61 192
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 192 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 192 277 (accept_3_3 59 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 192 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 192 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 192 277 (accept_3_3 56 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 192 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 192 277
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 192 277 (accept_3_3 53 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 192 277 (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 192 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 192 277 (accept_3_3 50 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 192 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 192 277
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 192 277 (accept_3_3 47 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 192 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 192 277 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 192 277 (accept_3_3 44 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 192 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 192 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 192 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 192 277 (accept_3_3 41 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 192 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 192 277 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 192 277 (accept_3_3 38 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 192 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 192 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 192 277
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 192 277 (accept_3_3 35 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 192 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 192 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 192 277 (accept_3_3 32 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 192 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 192 277
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 192 277 (accept_3_3 29 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 192 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 192 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 192 277 (accept_3_3 26 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 277 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 192 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 192 277 (accept_3_3 23 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 192 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 192 277 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 192 277 (accept_3_3 20 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 192 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 192 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 192 277
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 192 277 (accept_3_3 17 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 192 277 (Polychromatic418967fa.accept_19_16_2_11_1_4705 16 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 192 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 192 277 (accept_3_3 14 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 277 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 277
  (Polychromatic418967fa.accept_21_12_3_4_1_4988 12 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 192 277 (accept_3_3 11 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 192 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 192 277 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 192 277 (accept_3_3 8 192 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 277 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 192 277
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 192 277 (accept_3_3 5 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  192 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 192 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 192 277 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 277 (accept_3_3 2 192 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 277 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 192 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 191 277
  (Eq.refl Bool.true) (allA_of_3_1 87 191 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 190 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 190 277 (accept_3_3 86 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 190 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 190 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 190 277 (accept_3_3 83 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 190 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 190 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 190 277 (accept_3_3 80 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 190 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 190 277 (accept_3_3 77 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 190 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 190 277 (accept_3_3 74 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 190 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 190 277
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 72 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 190 277 (accept_3_3 71 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 190 277 (Polychromatic418967fa.accept_17_2_3_5_1_763 70 190 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 190 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 190 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 190 277 (accept_3_3 68 190 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 67
  190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 190 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 190 277 (accept_3_3 65 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 190 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 190 277 (accept_3_3 62 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 190 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 190 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 190 277 (accept_3_3 59 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 190 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 190 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 190 277 (accept_3_3 56 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 190 277
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 190 277 (accept_3_3 53 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 190 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 190 277 (accept_3_3 50 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 190 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 190 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 190 277 (accept_3_3 47 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 190 277 (Polychromatic418967fa.accept_14_4_8_11_1_794 46 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 190 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 190 277 (accept_3_3 44 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 190 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 190 277 (accept_3_3 41 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 190 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 190 277 (accept_3_3 38 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 190 277 (Polychromatic418967fa.accept_13_11_8_4_1_3950 37 190 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 190 277
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 190 277 (accept_3_3 35 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 190 277 (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 190 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 190 277 (accept_3_3 32 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 190 277
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 190 277 (accept_3_3 29 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 190 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 190 277 (accept_3_3 26 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 190 277 (Polychromatic418967fa.accept_13_12_8_4_1_3099 25 190 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 190 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 190 277 (accept_3_3 23 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 190 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 190 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 190 277 (accept_3_3 20 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 190 277
  (Polychromatic418967fa.accept_14_4_8_11_1_794 18 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 190 277 (accept_3_3 17 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 190 277 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 190 277 (accept_3_3 14 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 190 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 190 277
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 190 277 (accept_3_3 11 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 190 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 190 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 190 277 (accept_3_3 8 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 277
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 190 277 (accept_3_3 5 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  190 277 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 190 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 190 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 277 (accept_3_3 2 190 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 190 277 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 190 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190
  277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 189 277
  (Eq.refl Bool.true) (allA_succ_of_accept 88 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 189 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 87 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 189 277 (accept_3_3 86 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 189 277 (Polychromatic418967fa.accept_28_1_21_25_1_17031 85 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 189 277 (Polychromatic418967fa.accept_13_6_7_4_1_2264 84 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 189 277 (accept_3_3 83 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 189 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 189 277
  (Polychromatic418967fa.accept_13_3_7_4_1_435 81 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 189 277 (accept_3_3 80 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 189 277 (Polychromatic418967fa.accept_19_3_18_11_1_6074 79 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 189 277 (Polychromatic418967fa.accept_10_8_9_7_1_1118 78 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 189 277 (accept_3_3 77 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 189 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 189 277
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 189 277 (accept_3_3 74 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 189 277 (Polychromatic418967fa.accept_14_3_7_11_1_765 73 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 189 277 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 189 277 (accept_3_3 71 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 189 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 189 277
  (Polychromatic418967fa.accept_19_12_18_11_1_9065 69 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 189 277 (accept_3_3 68 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 189 277 (Polychromatic418967fa.accept_17_16_2_5_1_6031 67 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 189 277 (Polychromatic418967fa.accept_14_10_7_11_1_3015 66 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 189 277 (accept_3_3 65 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 277
  (Polychromatic418967fa.accept_6_4_3_1_1_57 64 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 189 277 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 189 277 (accept_3_3 62 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 189 277 (Polychromatic418967fa.accept_13_9_7_4_1_953 61 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 189 277
  (Polychromatic418967fa.accept_14_4_7_11_1_790 60 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 189 277 (accept_3_3 59 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 189 277 (Polychromatic418967fa.accept_16_9_13_5_1_2238 57 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 189 277 (accept_3_3 56 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 189 277 (Polychromatic418967fa.accept_13_3_7_4_1_435 55 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 189 277
  (Polychromatic418967fa.accept_17_3_2_5_1_2556 54 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 189 277 (accept_3_3 53 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 189 277 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 189 277 (accept_3_3 50 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 189 277 (Polychromatic418967fa.accept_13_10_7_4_1_2262 49 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 189 277
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 189 277 (accept_3_3 47 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 189 277 (Polychromatic418967fa.accept_13_6_7_4_1_2264 45 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 189 277 (accept_3_3 44 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 277 (Polychromatic418967fa.accept_15_13_9_7_1_2194 43 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 277
  (Polychromatic418967fa.accept_10_2_9_7_1_720 42 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 189 277 (accept_3_3 41 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 189 277 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 189 277 (accept_3_3 38 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 277 (Polychromatic418967fa.accept_13_11_7_4_1_1561 37 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 277
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 189 277 (accept_3_3 35 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 189 277 (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 277 (accept_3_3 32 189 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 277 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 277
  (Polychromatic418967fa.accept_20_10_9_17_1_12902 30 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 189 277 (accept_3_3 29 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 277 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 277 (accept_3_3 26 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 277
  (Polychromatic418967fa.accept_13_12_7_4_1_3124 25 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 189 277 (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 277 (accept_3_3 23 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 189 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 277 (Polychromatic418967fa.accept_18_3_9_7_1_1839
  21 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 277 (accept_3_3 20
  189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 277
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 19 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 189 277 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 277 (accept_3_3 17 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 189 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 277 (Polychromatic418967fa.accept_12_3_9_1_1_290
  15 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 277 (accept_3_3 14
  189 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 277
  (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 189 277 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 277 (accept_3_3 11 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 189 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 277 (Polychromatic418967fa.accept_13_9_7_4_1_953 9
  189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 277 (accept_3_3 8 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 277
  (Polychromatic418967fa.accept_19_7_18_11_1_464 7 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 189 277 (Polychromatic418967fa.accept_13_6_7_4_1_2264 6 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 277 (accept_3_3 5 189 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 189 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 277 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 277 (accept_3_3 2 189
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 277
  (Polychromatic418967fa.accept_15_1_9_7_1_3130 1 189 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 189 277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  90 188 277 (Eq.refl Bool.true) (allA_of_3_1 90 188 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 187 277
  (Eq.refl Bool.true) (allA_succ_of_accept 90 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 187 277 (accept_3_3 89 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 187 277 (Polychromatic418967fa.accept_13_10_5_4_1_3107 88 187
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 187 277
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 87 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 187 277 (accept_3_3 86 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 187 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 187 277 (Polychromatic418967fa.accept_13_6_5_4_1_3924 84 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 187 277 (accept_3_3 83 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 187 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 187 277
  (Polychromatic418967fa.accept_19_5_16_11_1_4727 81 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 187 277 (accept_3_3 80 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 187 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 187 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 187 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 187 277 (accept_3_3 77 187 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 187 277 (Polychromatic418967fa.accept_7_6_5_4_1_297
  76 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 187 277
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 75 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 187 277 (accept_3_3 74 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 187 277 (Polychromatic418967fa.accept_16_9_11_5_1_2279 73 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 187 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 187 277 (accept_3_3 71 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 187 277
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 187 277 (accept_3_3 68 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 187 277 (Polychromatic418967fa.accept_13_2_5_4_1_3926 67 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 187 277 (accept_3_3 65 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 187 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 187 277
  (Polychromatic418967fa.accept_19_6_16_11_1_9041 63 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 187 277 (accept_3_3 62 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 187 277 (Polychromatic418967fa.accept_13_9_5_4_1_1591 61 187 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 187 277 (Polychromatic418967fa.accept_21_18_19_4_1_4979 60 187
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 187 277 (accept_3_3 59 187
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2
  58 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 187 277
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 187 277 (accept_3_3 56 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 187 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 187 277 (accept_3_3 53 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 187 277 (Polychromatic418967fa.accept_19_14_16_11_1_9054 52 187 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 187 277
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 187 277 (accept_3_3 50 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 187 277 (Polychromatic418967fa.accept_13_10_5_4_1_3107 49 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 187 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 187 277 (accept_3_3 47 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 187 277
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 45 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 187 277 (accept_3_3 44 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 187 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 277 (accept_3_3 41 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 187 277 (Polychromatic418967fa.accept_13_1_5_4_1_463 40 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 277
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 39 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 187 277 (accept_3_3 38 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 187 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 187 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 277 (accept_3_3 35 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 187 277
  (Polychromatic418967fa.accept_19_14_16_11_1_9054 33 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 187 277 (accept_3_3 32 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 187 277 (Polychromatic418967fa.accept_21_10_19_4_1_8121 31 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 277 (accept_3_3 29
  187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 277
  (Polychromatic418967fa.accept_13_2_5_4_1_3926 28 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 187 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 187 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 277 (accept_3_3 26 187 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 187 277 (Polychromatic418967fa.accept_13_12_5_4_1_3133 25 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 277
  (Polychromatic418967fa.accept_16_8_11_5_1_3319 24 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 277 (accept_3_3 23 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 277 (Polychromatic418967fa.accept_19_2_16_11_1_6045 21 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 277 (accept_3_3 20 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 277 (Polychromatic418967fa.accept_13_6_5_4_1_3924 19 187
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 277
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 187 277 (accept_3_3 17 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 187 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 187 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 277 (accept_3_3 14 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 277 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 277
  (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 277 (accept_3_3 11 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 277 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 277 (accept_3_3 8 187 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 277 (Polychromatic418967fa.accept_16_7_11_5_1_4402 7 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 277
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 277 (accept_3_3 5 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 277 (Polychromatic418967fa.accept_19_4_16_11_1_6046 4 187 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 277 (Polychromatic418967fa.accept_22_3_11_13_1_9262 3 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 277 (accept_3_3 2 187 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 277 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 187 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187
  277))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 186 277
  (Eq.refl Bool.true) (allA_succ_of_accept 91 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 186 277
  (Polychromatic418967fa.accept_19_14_15_11_1_4739 90 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 186 277 (accept_3_3 89 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 186 277 (Polychromatic418967fa.accept_15_13_6_7_1_1369 88 186 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 186 277 (accept_3_3 86 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 186 277 (Polychromatic418967fa.accept_9_4_6_7_1_286
  85 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 186 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 186 277 (accept_3_3 83 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 186 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 186 277 (Polychromatic418967fa.accept_10_1_6_7_1_710 81 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 186 277 (accept_3_3 80 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 186 277
  (Polychromatic418967fa.accept_11_1_10_2_1_58 78 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 186 277 (accept_3_3 77 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 186 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 186 277 (accept_3_3 74 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 186 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 186 277
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 72 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 186 277 (accept_3_3 71 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 186 277 (Polychromatic418967fa.accept_17_2_16_5_1_1584 70 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 186 277 (Polychromatic418967fa.accept_17_1_16_5_1_3670 69 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 186 277 (accept_3_3 68 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 186 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 186 277 (accept_3_3 65 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 186 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 186 277 (accept_3_3 62 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 186 277 (Polychromatic418967fa.accept_10_1_6_7_1_710 61 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 186 277
  (Polychromatic418967fa.accept_16_12_10_5_1_5457 60 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 186 277 (accept_3_3 59 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 186 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 186 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 186 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 186 277 (accept_3_3 56 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 55
  186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 186 277
  (Polychromatic418967fa.accept_19_16_15_11_1_7684 54 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 186 277 (accept_3_3 53 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 186 277 (Polychromatic418967fa.accept_17_1_16_5_1_3670 52 186 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 186 277 (accept_3_3 50 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 186 277 (Polychromatic418967fa.accept_9_4_6_7_1_286
  49 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 186 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 186 277 (accept_3_3 47 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 186 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 186 277 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 186 277 (accept_3_3 44 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 186 277
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 42 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 186 277 (accept_3_3 41 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 186 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 186 277 (accept_3_3 38 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 186 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 186 277
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 186 277 (accept_3_3 35 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 186 277 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 186 277 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 186 277 (accept_3_3 32 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 186 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 186 277 (accept_3_3 29 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 186 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 277 (accept_3_3 26 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 186 277 (Polychromatic418967fa.accept_19_6_15_11_1_4738 25 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 186 277
  (Polychromatic418967fa.accept_19_5_15_11_1_7568 24 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 186 277 (accept_3_3 23 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 186 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 186 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 186 277 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 277 (accept_3_3 20 186 277
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 19
  186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 277
  (Polychromatic418967fa.accept_17_1_16_5_1_3670 18 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 186 277 (accept_3_3 17 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 186 277 (Polychromatic418967fa.accept_15_1_6_7_1_6282 16 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 277 (accept_3_3 14 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 277
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 186 277 (accept_3_3 11 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 186 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 186 277 (Polychromatic418967fa.accept_18_9_6_7_1_6719 9 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 277 (accept_3_3 8 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 277
  (Polychromatic418967fa.accept_19_6_15_11_1_4738 6 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 186 277 (accept_3_3 5 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  186 277 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 186 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 186 277 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 277 (accept_3_3 2 186 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 277 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 186 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 185 277
  (Eq.refl Bool.true) (allA_of_3_1 93 185 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 184 277 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 184 277 (accept_3_3 92 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 184 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 184 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 90 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 184 277 (accept_3_3 89 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 184 277 (Polychromatic418967fa.accept_18_16_4_7_1_2927 88 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 184 277 (accept_3_3 86 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 184 277 (Polychromatic418967fa.accept_15_10_4_7_1_3127 85 184 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 184 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 184 277 (accept_3_3 83 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 184 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 184 277 (accept_3_3 80 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 184 277 (Polychromatic418967fa.accept_14_9_2_11_1_780 79 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 184 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 184 277 (accept_3_3 77 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 184 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 184 277 (accept_3_3 74 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 184 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 184 277
  (Polychromatic418967fa.accept_10_2_4_7_1_352 72 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 184 277 (accept_3_3 71 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 184 277 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 184 277 (accept_3_3 68 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 184 277 (Polychromatic418967fa.accept_16_3_8_5_1_6790 67 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 184 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 184 277 (accept_3_3 65 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 184 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 184 277 (accept_3_3 62 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 184 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 184 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 184 277 (accept_3_3 59 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 184 277 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 184 277 (accept_3_3 56 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 184 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 184 277
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 184 277 (accept_3_3 53 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 184 277 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 184 277 (accept_3_3 50 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 184 277 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 184 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 184 277 (accept_3_3 47 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 184 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 184 277 (accept_3_3 44 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 184 277 (Polychromatic418967fa.accept_10_3_4_7_1_353 43 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 184 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 184 277 (accept_3_3 41 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 184 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 184 277 (accept_3_3 38 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 184 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 184 277
  (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 184 277 (accept_3_3 35 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 184 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 184 277 (accept_3_3 32 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 184 277 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 184 277
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 184 277 (accept_3_3 29 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 184 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 184 277 (accept_3_3 26 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 184 277 (Polychromatic418967fa.accept_13_12_2_4_1_3131 25 184 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 184 277
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 184 277 (accept_3_3 23 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 184 277 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 184 277 (accept_3_3 20 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 184 277 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 184 277
  (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 184 277 (accept_3_3 17 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 184 277 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 184 277 (accept_3_3 14 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 184 277 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 184 277
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 184 277 (accept_3_3 11 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 184 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 184 277 (accept_3_3 8 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 184 277 (Polychromatic418967fa.accept_19_7_13_11_1_1208 7 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 184 277
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 184 277 (accept_3_3 5 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  184 277 (Polychromatic418967fa.accept_16_4_8_5_1_3317 4 184 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 184 277 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 277 (accept_3_3 2 184 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 277 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 184 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184
  277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 183
  277 (Eq.refl Bool.true) (allA_succ_of_accept 94 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 183 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 93 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 183 277 (accept_3_3 92 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 183 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 91 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 183 277 (accept_3_3 89 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 183 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 183 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 87 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 183 277 (accept_3_3 86 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 183 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 85 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 183 277 (Polychromatic418967fa.accept_10_4_3_7_1_1110 84 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 183 277 (accept_3_3 83 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 183 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 183 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 81 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 183 277 (accept_3_3 80 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 183 277 (Polychromatic418967fa.accept_15_4_3_7_1_713 79 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 183 277 (accept_3_3 77 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 183 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 183 277
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 183 277 (accept_3_3 74 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 183 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 183 277 (Polychromatic418967fa.accept_15_12_3_7_1_4123 72 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 183 277 (accept_3_3 71 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 183 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 183 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 183 277 (accept_3_3 68 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 183 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 183 277 (accept_3_3 65 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 183 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 183 277
  (Polychromatic418967fa.accept_18_9_3_7_1_9449 63 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 183 277 (accept_3_3 62 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 183 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 183 277 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 183 277 (accept_3_3 59 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 183 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 183 277 (accept_3_3 56 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 183 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 183 277 (accept_3_3 53 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 183 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 183 277 (accept_3_3 50 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 183 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 183 277 (Polychromatic418967fa.accept_18_12_3_7_1_5373 48 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 183 277 (accept_3_3 47 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 183 277
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 183 277 (accept_3_3 44 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 183 277 (Polychromatic418967fa.accept_16_11_7_5_1_4364 43 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 277 (accept_3_3 41 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 277
  (Polychromatic418967fa.accept_19_1_12_11_1_1245 39 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 183 277 (accept_3_3 38 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 183 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 183 277 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 277 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 183
  277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 277 (accept_3_3 35 183
  277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2
  34 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 277
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 183 277 (accept_3_3 32 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 183 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 277 (accept_3_3 29 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 277
  (Polychromatic418967fa.accept_15_12_3_7_1_4123 27 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 183 277 (accept_3_3 26 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 183 277 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 183 277 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 277 (accept_3_3 23 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 277
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 277 (accept_3_3 20 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 183 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 277 (accept_3_3 17 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 277
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 183 277 (accept_3_3 14 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 183 277 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 183 277 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 277 (accept_3_3 11 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 277
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 183 277 (accept_3_3 8 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  183 277 (Polychromatic418967fa.accept_19_7_12_11_1_7621 7 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 183 277 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 277 (accept_3_3 5 183 277 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 277 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 277 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 277
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 277 (accept_3_3 2 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 277 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 183 277 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183
  277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_277_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


