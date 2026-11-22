-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch285
-- name    : Polychromatic418967fa_Branch285
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:34:14.5282+00:00
-- url     : https://prove2.me/theorems/a88c2134-ac28-48b7-abb0-64cd08801b0f
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch285_Segment003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_285 : allB 285 285 :=
  allB_succ' 2 284 285 (Eq.refl Bool.true) (allA_succ_of_accept 1 284 285 (accept_3_4 1 284 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 284 285)) (allB_succ' 3 283 285 (Eq.refl Bool.true) (allA_succ_of_accept 2 283 285
  (accept_3_5 2 283 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 283 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 283 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 283 285))) (allB_succ' 4 282 285 (Eq.refl Bool.true) (allA_succ_of_gcd 3 282 285 3 1 94 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 282 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 282 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 282 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 282 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 282 285)))) (allB_succ' 5 281 285 (Eq.refl Bool.true) (allA_succ_of_accept 4
  281 285 (accept_3_4 4 281 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 281 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 281 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 281 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 281 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 281 285 (accept_3_4 1 281 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 281 285))))) (allB_succ' 6 280 285 (Eq.refl Bool.true) (allA_succ_of_gcd 5 280 285 5 1 56 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 280 285
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 280 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 280 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 280 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 280 285 (accept_3_5 2 280 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 280 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 280 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 280 285)))))) (allB_succ' 7 279 285 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 279 285 3 2 93 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 279 285 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 279 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 279 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 279 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 279 285 3 1 93 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 279 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 279 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 279 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 279 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 279 285))))))) (allB_succ' 8 278 285 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 278 285 (accept_3_4 7 278 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  278 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 278 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 278 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 278 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 278 285 (accept_3_4 4 278 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 278 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 278 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 278 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 278 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 278 285 (accept_3_4 1 278 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 278
  285)))))))) (allB_succ' 9 277 285 (Eq.refl Bool.true) (allA_succ_of_accept 8 277 285 (accept_3_5 8 277 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 277 285 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 277
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 277 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 277 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 277 285 (accept_3_5 5 277 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  277 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 277 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 277 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 277 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 277 285 (accept_3_5 2 277 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 277 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 277 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 277 285))))))))) (allB_succ' 10 276 285 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 276 285 3 3 92 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 276 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 276 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 276 285 (Polychromatic418967fa.accept_16_7_4_13_1_1057
  7 276 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 276 285 3 2 92 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 276 285
  (Polychromatic418967fa.accept_18_5_6_15_1_3413 5 276 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 276 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 276 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 276 285 3 1 92 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 276 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 276 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 276 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 276 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 276 285)))))))))) (allB_succ' 11 275 285 (Eq.refl Bool.true) (allA_succ_of_gcd 10 275 285 5 2 55 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 275 285
  (Polychromatic418967fa.accept_18_9_5_15_1_2246 9 275 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 275 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 275 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 275 285 (accept_3_4 7 275 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 275 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 275 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 275 285 5 1 55 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 275 285 (accept_3_4 4 275 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 275 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 275 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 275 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 275 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 275 285 (accept_3_4 1 275 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 275
  285))))))))))) (allB_succ' 12 274 285 (Eq.refl Bool.true) (allA_succ_of_accept 11 274 285 (accept_3_5 11 274 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 274 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 10
  274 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 274 285
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 274 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 274 285 (accept_3_5 8 274 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  274 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 274 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 274 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 274 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 274 285 (accept_3_5 5 274 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 274 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 274 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 274 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 274 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 274 285 (accept_3_5 2 274 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  274 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 274 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 274 285)))))))))))) (allB_succ' 13 273 285 (Eq.refl Bool.true) (allA_succ_of_gcd 12 273 285 3 4
  91 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 273 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 273 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 273 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 273 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 273 285 3 3 91 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 273 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 273 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 273 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 273 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 273 285 3 2 91 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 273 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 273 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 273 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 273 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 273 285 3 1 91 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 273 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 273 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 273 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 273 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 273 285))))))))))))) (allB_succ' 14 272 285 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 272 285 (accept_3_4 13 272 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 272 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 272 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 272 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 272 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 272 285 (accept_3_4 10 272 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 272 285 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 272 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 272 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 272 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 272 285 (accept_3_4 7 272 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  272 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 272 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 272 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 272 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 272 285 (accept_3_4 4 272 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 272 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 272 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 272 285
  (Polychromatic418967fa.accept_22_2_8_21_1_16092 2 272 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 272 285 (accept_3_4 1 272 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 272
  285)))))))))))))) (allB_succ' 15 271 285 (Eq.refl Bool.true) (allA_succ_of_accept 14 271 285 (accept_3_5 14 271 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 271 285 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 271 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 271 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 271 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 271 285 (accept_3_5 11 271 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 271 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 271 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 271 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 271 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 271 285 (accept_3_5 8 271 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 271 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 271 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 271 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 271 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 271 285 (accept_3_5 5 271 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  271 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 271 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 271 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 271 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 271 285 (accept_3_5 2 271 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 271 285 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 271 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 271 285))))))))))))))) (allB_succ' 16 270 285 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 270 285 15 1 18 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 270 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 270 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 270 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 270 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 270 285 3 4 90 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 270 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 270 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 270 285 5 2 54 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 270 285 3 3 90 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 270 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 8
  270 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 270 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 270 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 270 285 3 2 90 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 270 285 5 1 54 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 270 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 270 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 270 285 3 1 90 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 270 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 270 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 270 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 270 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 270 285)))))))))))))))) (allB_succ' 17 269 285 (Eq.refl Bool.true) (allA_succ_of_accept 16 269 285
  (accept_3_4 16 269 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 269 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 269 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 269 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 269 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 269 285 (accept_3_4 13 269 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 269 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 269 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 269 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 11
  269 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 269 285 (accept_3_4 10
  269 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 269 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 269 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 269 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 269 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 269 285 (accept_3_4 7 269 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 269 285 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 269 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 269 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 5
  269 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 269 285 (accept_3_4 4 269
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 269 285 (Polychromatic418967fa.accept_9_3_8_6_1_80
  3 269 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 269 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 269 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 269 285 (accept_3_4 1 269 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 269
  285))))))))))))))))) (allB_succ' 18 268 285 (Eq.refl Bool.true) (allA_succ_of_accept 17 268 285 (accept_3_5 17 268 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 268 285 (Polychromatic418967fa.accept_11_5_4_10_1_524
  16 268 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 268 285
  (Polychromatic418967fa.accept_16_15_12_13_1_1045 15 268 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 268 285 (accept_3_5 14 268 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 268 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 268 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 268 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 268 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 268 285 (accept_3_5 11 268 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 268 285 (Polychromatic418967fa.accept_7_3_2_5_1_147
  10 268 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 268 285
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 268 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 268 285 (accept_3_5 8 268 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  268 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 268 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 268 285 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 268 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 268 285 (accept_3_5 5 268 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 268 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 268 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 268 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 268 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 268 285 (accept_3_5 2 268 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  268 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 268 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 268 285)))))))))))))))))) (allB_succ' 19 267 285 (Eq.refl Bool.true) (allA_succ_of_gcd 18 267
  285 3 6 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  267 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 267 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 267 285 (Polychromatic418967fa.accept_17_16_12_13_1_3070 16 267 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 267 285 3 5 89 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 267 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 267 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 267 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 267 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 267 285 3 4 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 267 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 11
  267 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 267 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 267 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 267 285 3 3 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 267 285 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 267 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 267 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 267
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 267 285 3 2 89 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 267 285
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 267 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 267 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 267 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 267 285 3 1 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 267 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 267 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 285
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 267 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 267 285))))))))))))))))))) (allB_succ' 20 266 285 (Eq.refl Bool.true) (allA_succ_of_gcd 19 266 285 19 1 14
  15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18 266 285
  (Polychromatic418967fa.accept_12_6_2_9_1_537 18 266 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 266 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 266 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 266 285 (accept_3_4 16 266 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 266 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 266 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 266 285 (Polychromatic418967fa.accept_10_4_6_5_1_74
  14 266 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 266 285 (accept_3_4 13
  266 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 266 285
  (Polychromatic418967fa.accept_9_3_5_6_1_253 12 266 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 266 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 266 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 266 285 (accept_3_4 10 266 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 266 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 266 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 266 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  266 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 266 285 (accept_3_4 7 266
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 266 285
  (Polychromatic418967fa.accept_12_6_2_9_1_537 6 266 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 266 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 266 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 266 285 (accept_3_4 4 266 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 266 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 266 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 266 285 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  266 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 266 285 (accept_3_4 1 266
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 266 285)))))))))))))))))))) (allB_succ' 21 265 285 (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 265 285 5 4 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 265 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 265 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 265 285 (Polychromatic418967fa.accept_7_4_6_5_1_141
  18 265 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 265 285 (accept_3_5 17
  265 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 265 285
  (Polychromatic418967fa.accept_6_4_1_3_1_77 16 265 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 265 285 5 3 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 265 285 (accept_3_5 14 265 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 265 285 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 265 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 265 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 265 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 265 285 (accept_3_5 11 265 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 265 285 5 2 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 265 285 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 265 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 265 285 (accept_3_5 8 265 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 265 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 7
  265 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 265 285
  (Polychromatic418967fa.accept_13_6_5_12_1_307 6 265 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 265 285 5 1 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 265 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 265 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 265 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 265 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 265 285 (accept_3_5 2 265 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 265 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 1
  265 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 265 285)))))))))))))))))))))
  (allB_succ' 22 264 285 (Eq.refl Bool.true) (allA_succ_of_gcd 21 264 285 3 7 88 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 264 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 264 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 264 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 264 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 264 285 3 6 88 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 264 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  264 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 264 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 264 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 264 285 3 5 88 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 264 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 264 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 264 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 264 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 264 285 3 4 88 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 264 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 264 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 264 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 264 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 264 285 3 3 88 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 264 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 264 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 264 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 264 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 264 285 3 2 88 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 264 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 264 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 264 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 264 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 264 285 3 1 88 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 264 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 264 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 264 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 264 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 264 285)))))))))))))))))))))) (allB_succ' 23 263 285 (Eq.refl Bool.true)
  (allA_succ_of_accept 22 263 285 (accept_3_4 22 263 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 263 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 263 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 263 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 263 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 263 285 (accept_3_4 19 263 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 263 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 263 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 263 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 263 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 263 285 (accept_3_4 16 263 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 263 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 263 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 263 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 263 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 263 285 (accept_3_4 13 263 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 263 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 263 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 263 285
  (Polychromatic418967fa.accept_33_11_32_21_1_17510 11 263 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 263 285 (accept_3_4 10 263 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 263 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 263 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 263 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 263 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 263 285 (accept_3_4 7 263 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 263 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  263 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 263 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 263 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 263 285 (accept_3_4 4 263 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  263 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 263 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 263 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 263 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 263 285 (accept_3_4 1 263 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 263 285))))))))))))))))))))))) (allB_succ' 24 262 285 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 262 285 (accept_3_5 23 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 262 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 262 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 262 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 262 285 (accept_3_5 20 262 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 262 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 262 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 262 285
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 262 285 (accept_3_5 17 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 262 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 262 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 262 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 262 285 (accept_3_5 14 262 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 262 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 262 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 262 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 262 285 (accept_3_5 11 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 262 285 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 262 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 262 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 262 285 (accept_3_5 8 262 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 262 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 262 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 262 285
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 262 285 (accept_3_5 5 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  262 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 262 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 262 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 262 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 262 285 (accept_3_5 2 262 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 262 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 262 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 262 285)))))))))))))))))))))))) (allB_succ' 25 261 285
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 261 285 3 8 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 261 285 (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 261 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 261 285
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 22 261 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 261 285 3 7 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 261 285 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 261 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 261 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 261
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 261 285 3 6 87 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 261 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 261 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 261 285 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 261 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 261 285 3 5 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 261 285 (Polychromatic418967fa.accept_10_4_1_5_1_1018
  14 261 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 261 285
  (Polychromatic418967fa.accept_21_13_9_12_1_4038 13 261 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 261 285 3 4 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 261 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 261 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 261 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 10 261 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 261 285 3 3 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 261 285 (Polychromatic418967fa.accept_13_8_1_12_1_762 8 261 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 261 285 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 261 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 261 285 3 2 87 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 261 285
  (Polychromatic418967fa.accept_13_5_1_12_1_740 5 261 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 261 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 261 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 261 285 3 1 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 261 285 (Polychromatic418967fa.accept_13_2_1_12_1_1326 2 261 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 261 285
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 1 261 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 261 285))))))))))))))))))))))))) (allB_succ' 26 260 285 (Eq.refl Bool.true) (allA_succ_of_gcd 25 260 285 5 5
  52 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 260 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 260 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 260 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 260 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 260 285 (accept_3_4 22 260 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 260 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 260 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 260 285 5 4 52 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 260 285 (accept_3_4 19 260 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 260 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 260 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 260 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 260 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 260 285 (accept_3_4 16 260 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  260 285 5 3 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 260 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 260 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 260 285 (accept_3_4 13 260 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 260 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 260 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 260 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 260 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 260 285 5 2 52 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 260 285
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 260 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 260 285 (Polychromatic418967fa.accept_16_8_4_13_1_1014 8 260 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 260 285 (accept_3_4 7 260 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 260 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 260 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 260 285 5 1 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 260 285 (accept_3_4 4 260 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 260 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 260 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 260 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 260 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 260 285 (accept_3_4 1 260 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 260
  285)))))))))))))))))))))))))) (allB_succ' 27 259 285 (Eq.refl Bool.true) (allA_succ_of_accept 26 259 285 (accept_3_5
  26 259 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 259 285
  (Polychromatic418967fa.accept_17_8_4_13_1_3014 25 259 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 259 285 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 259 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 259 285 (accept_3_5 23 259 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 259 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 259 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 259 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  259 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 259 285 (accept_3_5 20
  259 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 259 285
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 259 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 259 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 259 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 259 285 (accept_3_5 17 259 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 259 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 259 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 259 285 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  15 259 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 259 285 (accept_3_5 14
  259 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 259 285
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 259 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 259 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 259 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 259 285 (accept_3_5 11 259 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 259 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 259 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 259 285 (Polychromatic418967fa.accept_14_9_7_5_1_1105
  9 259 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 259 285 (accept_3_5 8
  259 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 259 285
  (Polychromatic418967fa.accept_22_7_17_21_1_14503 7 259 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 259 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 259 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 259 285 (accept_3_5 5 259 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 259 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 259 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 259 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 259 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 259 285 (accept_3_5 2 259 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  259 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 259 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 259 285))))))))))))))))))))))))))) (allB_succ' 28 258 285 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 258 285 3 9 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 258 285 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 258 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 258 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 258 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 258 285 3 8 86 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 258 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 258 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 258 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 258 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 258 285 3 7 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 258 285 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 258 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 258 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 258 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 258 285 3 6 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 258 285 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 258 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 258 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 258
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 258 285 3 5 86 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 258 285
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 258 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 258 285 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 258 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 258 285 3 4 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 258 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  258 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 258 285
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 258 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 258 285 3 3 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 258 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 258 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 258 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 258 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 258 285 3 2 86 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 258 285
  (Polychromatic418967fa.accept_16_5_2_13_1_1007 5 258 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 258 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 258 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 258 285 3 1 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 258 285 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 258 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 258 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 258 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 258 285)))))))))))))))))))))))))))) (allB_succ' 29 257 285 (Eq.refl Bool.true) (allA_succ_of_accept 28 257
  285 (accept_3_4 28 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 257 285
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 257 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 257 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 257 285 (accept_3_4 25 257 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 257 285 (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 257 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 257 285
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 257 285 (accept_3_4 22 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 257 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 257 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 257 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 257 285 (accept_3_4 19 257 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 257 285 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 257 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 257 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 257 285 (accept_3_4 16 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 257 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 257 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 257 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 257 285 (accept_3_4 13 257 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 257 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 257 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 257 285
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 257 285 (accept_3_4 10 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  257 285 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 257 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 257 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 257 285 (accept_3_4 7 257 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 257 285 (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 257 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 257 285
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 257 285 (accept_3_4 4 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  257 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 257 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 257 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 257 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 257 285 (accept_3_4 1 257 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 257 285))))))))))))))))))))))))))))) (allB_succ' 30 256 285 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 256 285 (accept_3_5 29 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 256 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 256 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 256 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 256 285 (accept_3_5 26 256 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 256 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 256 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 256 285
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 256 285 (accept_3_5 23 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 256 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 256 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 256 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 256 285 (accept_3_5 20 256 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 256 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 256 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 256 285
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 256 285 (accept_3_5 17 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 256 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 256 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 256 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 256 285 (accept_3_5 14 256 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 256 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 256 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 256 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 256 285 (accept_3_5 11 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 256 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 256 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 256 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 256 285 (accept_3_5 8 256 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 256 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 256 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 256 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 256 285 (accept_3_5 5 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  256 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 256 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 256 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 256 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 256 285 (accept_3_5 2 256 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 256 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 256 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 256 285)))))))))))))))))))))))))))))) (allB_succ' 31 255
  285 (Eq.refl Bool.true) (allA_succ_of_gcd 30 255 285 15 2 17 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 255 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 255 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 255 285
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 255 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 255 285 3 9 85 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 255 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 255 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 255 285 5 5 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 255 285 3 8 85 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 255 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 23
  255 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 255 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 255 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 255 285 3 7 85 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 255 285 5 4 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 255 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 255 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 255 285 3 6 85 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 255 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  255 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 255 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 255 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 255 285 15 1 17 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 255 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 255 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 255 285 (Polychromatic418967fa.accept_9_4_3_6_1_532
  13 255 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 255 285 3 4 85 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 255 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 255 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 255 285 5 2 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 255 285 3 3 85 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 255 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 255 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 255 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 255 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 255 285 3 2 85 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 255 285 5 1 51 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 255 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 255 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 255 285 3 1 85 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 255 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 255 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 255 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 255 285)))))))))))))))))))))))))))))))
  (allB_succ' 32 254 285 (Eq.refl Bool.true) (allA_succ_of_accept 31 254 285 (accept_3_4 31 254 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 254 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 254 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 254 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 254 285 (accept_3_4 28 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 254 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 254 285 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 254 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 254 285 (accept_3_4 25 254 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 254 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 254 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 254 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 254 285 (accept_3_4 22 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 254 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 254 285 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 254 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 254 285 (accept_3_4 19 254 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 254 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 254 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 254 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 254 285 (accept_3_4 16 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 254 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 254 285 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 254 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 254 285 (accept_3_4 13 254 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 254 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 254 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 254 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 254 285 (accept_3_4 10 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  254 285 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 254 285 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 254 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 254 285 (accept_3_4 7 254 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 254 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 254 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 254 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 254 285 (accept_3_4 4 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  254 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 254 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 254 285 (Polychromatic418967fa.accept_11_2_1_10_1_196 2 254 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 254 285 (accept_3_4 1 254 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 254 285)))))))))))))))))))))))))))))))) (allB_succ' 33 253 285 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 253 285 (accept_3_5 32 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 253 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 253 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 253 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 253 285 (accept_3_5 29 253 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 253 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 253 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 253 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 253 285 (accept_3_5 26 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 253 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 253 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 253 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 253 285 (accept_3_5 23 253 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 253 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 253 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 253 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 253 285 (accept_3_5 20 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 253 285 (Polychromatic418967fa.accept_17_2_15_13_1_3034 19 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 253 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 253 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 253 285 (accept_3_5 17 253 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 253 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 253 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 253 285
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 253 285 (accept_3_5 14 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 253 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 253 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 253 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 253 285 (accept_3_5 11 253 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 253 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 253 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 253 285
  (Polychromatic418967fa.accept_21_9_1_12_1_3984 9 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 253 285 (accept_3_5 8 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  253 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 253 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 253 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 253 285 (accept_3_5 5 253 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 253 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 253 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 253 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 253 285 (accept_3_5 2 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  253 285 (Polychromatic418967fa.accept_22_1_11_21_1_6612 1 253 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 253 285))))))))))))))))))))))))))))))))) (allB_succ' 34 252 285 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 252 285 3 11 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 252 285 (Polychromatic418967fa.accept_13_6_5_12_1_307 32 252 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 252 285
  (Polychromatic418967fa.accept_16_15_12_13_1_1045 31 252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 252 285 3 10 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 252 285 (Polychromatic418967fa.accept_22_7_10_21_1_17509 29 252 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 252 285
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 252 285 3 9 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 252 285 (Polychromatic418967fa.accept_16_10_12_13_1_4950 26 252 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 252 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 25
  252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 252 285 3 8 84 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 252 285
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 252 285 (Polychromatic418967fa.accept_27_22_9_15_1_17508 22 252 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 252 285 3 7 84 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 252 285
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 252 285 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 252 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 252 285 3 6 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 252 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 17
  252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 252 285
  (Polychromatic418967fa.accept_25_16_2_10_1_17507 16 252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 252 285 3 5 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 252 285 (Polychromatic418967fa.accept_13_1_5_12_1_306 14 252 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 252 285
  (Polychromatic418967fa.accept_10_3_2_5_1_295 13 252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 252 285 3 4 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 252 285 (Polychromatic418967fa.accept_22_11_10_21_1_17506 11 252 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 252 285
  (Polychromatic418967fa.accept_16_10_12_13_1_4950 10 252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 252 285 3 3 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 252 285 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 252 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 252 285 (Polychromatic418967fa.accept_10_7_2_5_1_298 7
  252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 252 285 3 2 84 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 252 285
  (Polychromatic418967fa.accept_25_5_2_10_1_17505 5 252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 252 285 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 252 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 252 285 3 1 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 252 285 (Polychromatic418967fa.accept_13_2_5_12_1_2043 2 252 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 252 285
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 252 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 252 285)))))))))))))))))))))))))))))))))) (allB_succ' 35 251 285 (Eq.refl Bool.true) (allA_succ_of_accept 34
  251 285 (accept_3_4 34 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 251 285
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 251 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 251 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 251 285 (accept_3_4 31 251 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 251 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 251 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 251 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 29
  251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 251 285 (accept_3_4 28
  251 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 251 285
  (Polychromatic418967fa.accept_12_3_11_9_1_193 27 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 251 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 251 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 251 285 (accept_3_4 25 251 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 251 285 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 251 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 251 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 251 285 (accept_3_4 22 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 251 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 251 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 251 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 251 285 (accept_3_4 19 251 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 251 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 251 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 251 285
  (Polychromatic418967fa.accept_20_17_11_5_1_4685 17 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 251 285 (accept_3_4 16 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 251 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 251 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 251 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 251 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 251 285 (accept_3_4 13 251 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 251 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12
  251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 251 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 251 285 (accept_3_4 10 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  251 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 251 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 251 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 251 285 (accept_3_4 7 251 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 251 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 251 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 251 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 251 285 (accept_3_4 4 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  251 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 251 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 251 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 251 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 251 285 (accept_3_4 1 251 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 251 285))))))))))))))))))))))))))))))))))) (allB_succ' 36 250 285 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 250 285 5 7 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 250 285 (Polychromatic418967fa.accept_20_14_10_5_1_2117 34 250 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 250 285
  (Polychromatic418967fa.accept_17_16_12_13_1_3070 33 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 250 285 (accept_3_5 32 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 250 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 250 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 250 285 5 6 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 250 285 (accept_3_5 29 250 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 250 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 250 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 250 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 250 285 (accept_3_5 26 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  250 285 5 5 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 250 285 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 250 285 (accept_3_5 23 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 250 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 250 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 250 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 250 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 250 285 5 4 50 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 250 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 250 285 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 250 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 250 285 (accept_3_5 17 250 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 250 285 (Polychromatic418967fa.accept_17_16_12_13_1_3070 16 250 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 250 285 5 3 50 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 250 285 (accept_3_5 14 250 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 250 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  250 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 250 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 250 285 (accept_3_5 11 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  250 285 5 2 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 250 285 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 250 285 (accept_3_5 8 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 250 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 250 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 250 285 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 250 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 250 285 5 1 50 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 250 285
  (Polychromatic418967fa.accept_9_4_7_6_1_255 4 250 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 250 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 250 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 250 285 (accept_3_5 2 250 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 250 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 250 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 250 285)))))))))))))))))))))))))))))))))))) (allB_succ' 37 249 285
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 249 285 3 12 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 249 285 (Polychromatic418967fa.accept_20_15_9_5_1_4684 35 249
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 249 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 249 285 3 11 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 249 285 (Polychromatic418967fa.accept_13_6_2_12_1_2802 32 249 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 249 285
  (Polychromatic418967fa.accept_10_1_9_5_1_83 31 249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 249 285 3 10 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 249 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 249 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 249 285 (Polychromatic418967fa.accept_8_4_1_5_1_186
  28 249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 249 285 3 9 83 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 249 285
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 249 285 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 249 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 249 285 3 8 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 249 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 23
  249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 249 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 22 249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 249 285 3 7 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 249 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 249 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 249 285 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 249
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 249 285 3 6 83 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 249 285
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 249 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 249 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 249 285 3 5 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 249 285 (Polychromatic418967fa.accept_10_4_9_5_1_84 14
  249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 249 285 3 4 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 249 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 249 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 249 285 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 249
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 249 285 3 3 83 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 249 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 249 285 (Polychromatic418967fa.accept_16_7_9_13_1_4948 7 249 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 249 285 3 2 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 249 285 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 249 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 285
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 249 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 249 285 3 1 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 249 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 249 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 249 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249 285)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 248 285 (Eq.refl Bool.true) (allA_succ_of_accept 37 248 285 (accept_3_4 37 248 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 248 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 248 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 248 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 248 285 (accept_3_4 34 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 248 285 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 248 285 (Polychromatic418967fa.accept_10_2_8_5_1_587 32 248 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 248 285 (accept_3_4 31 248 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 248 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 248 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 248 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 248 285 (accept_3_4 28 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 248 285 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 248 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 248 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 248 285 (accept_3_4 25 248 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 248 285 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 248 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 248 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 248 285 (accept_3_4 22 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 248 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 248 285 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 248 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 248 285 (accept_3_4 19 248 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 248 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 248 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 248 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 248 285 (accept_3_4 16 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 248 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 248 285 (Polychromatic418967fa.accept_17_14_10_13_1_4147 14 248 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 248 285 (accept_3_4 13 248 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 248 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 248 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 248 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 248 285 (accept_3_4 10 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  248 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 248 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 248 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 248 285 (accept_3_4 7 248 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 248 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 248 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 248 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 248 285 (accept_3_4 4 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  248 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 248 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 248 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 248 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 248 285 (accept_3_4 1 248 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 248 285)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 247 285 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 247 285 19 2 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 247 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 247 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 247 285
  (Polychromatic418967fa.accept_16_4_7_13_1_2795 36 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 247 285 (accept_3_5 35 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 247 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 247 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 247 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 247 285 (accept_3_5 32 247 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 247 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 247 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 247 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 247 285 (accept_3_5 29 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 247 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 247 285 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 247 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 247 285 (accept_3_5 26 247 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 247 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 247 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 247 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 247 285 (accept_3_5 23 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 247 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 247 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 247 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 247 285 (accept_3_5 20 247 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 19 247 285 19 1 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18 247 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 247 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 247 285 (accept_3_5 17 247 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 247 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 247 285
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 247 285 (accept_3_5 14 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 247 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 247 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 247 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 247 285 (accept_3_5 11 247 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 247 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 247 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 247 285
  (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 247 285 (accept_3_5 8 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  247 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 247 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 247 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 247 285 (accept_3_5 5 247 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 247 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 247 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 247 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 247 285 (accept_3_5 2 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  247 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 247 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 247 285))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 246 285 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 246 285 3 13 82 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 246 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 246 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 246 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 246 285 3 12 82 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 246 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 246 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 246 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 246 285 3 11 82 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 246 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 32
  246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 246 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 246 285 3 10 82 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 246 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 246 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 246 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 246 285 3 9 82 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 246 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 246 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 246 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 246 285 3 8 82 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 246 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 246 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 246 285 3 7 82 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 246 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 246 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 246 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 246 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 246 285 3 6 82 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 246 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 246 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 246 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 246 285 3 5 82 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 246 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 246 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 246 285 3 4 82 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 246 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 246 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 246 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 246 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 246 285 3 3 82 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 246 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 246 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 246 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 246 285 3 2 82 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 246 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 246 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 246 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 246 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 246 285 3 1 82 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 246 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 246 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 246 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246 285))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 245 285 (Eq.refl Bool.true) (allA_succ_of_gcd 40 245 285 5 8 49 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 245 285
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 245 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 245 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 245 285 (accept_3_4 37 245 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 245 285 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 245 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 245 285 5 7 49 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 245 285 (accept_3_4 34 245 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 245 285
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 245 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 245 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 245 285 (accept_3_4 31 245 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 245 285 5 6 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 245 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 245
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 245 285 (accept_3_4 28 245
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 245 285
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 245 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 245 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 245 285 5 5 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 245 285 (Polychromatic418967fa.accept_16_8_5_13_1_1021
  24 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 245 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 245 285 (accept_3_4 22 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 245 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 245 285 5 4 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 245 285 (accept_3_4 19 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 245 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 245 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 245 285 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 245 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 245 285 (accept_3_4 16 245 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 245 285 5 3 49 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 245 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 245 285 (accept_3_4 13 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 245 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 245 285 (Polychromatic418967fa.accept_17_11_7_13_1_11667 11 245 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 245 285 5 2 49 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 245 285
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 245 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 245 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 285 (accept_3_4 7 245 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 245 285 (Polychromatic418967fa.accept_17_6_7_13_1_3062 6 245 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 245 285 5 1 49 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 245 285 (accept_3_4 4 245 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 245 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 285 (accept_3_4 1 245 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245
  285))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 244 285 (Eq.refl Bool.true) (allA_succ_of_accept 41 244
  285 (accept_3_5 41 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 244 285
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 244 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 244 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 244 285 (accept_3_5 38 244 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 244 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 244 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 244 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 36
  244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 244 285 (accept_3_5 35
  244 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 244 285
  (Polychromatic418967fa.accept_9_7_1_6_1_261 34 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 244 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 244 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 244 285 (accept_3_5 32 244 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 244 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 244 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 244 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 30
  244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 244 285 (accept_3_5 29
  244 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 244 285
  (Polychromatic418967fa.accept_13_2_10_12_1_757 28 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 244 285 (Polychromatic418967fa.accept_14_13_6_5_1_1853 27 244 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 244 285 (accept_3_5 26 244 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 244 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 244 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 244 285
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 244 285 (accept_3_5 23 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 244 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 244 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 244 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 244 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 244 285 (accept_3_5 20 244 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 244 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 244 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 244 285 (accept_3_5 17 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 244 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 244 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 244 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 244 285 (accept_3_5 14 244 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 244 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 244 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 244 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 244 285 (accept_3_5 11 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 244 285 (Polychromatic418967fa.accept_20_10_4_5_1_6051 10 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 244 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 244 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 244 285 (accept_3_5 8 244 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 244 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 244 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 244 285
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 244 285 (accept_3_5 5 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  244 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 244 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 244 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 244 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 244 285 (accept_3_5 2 244 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 244 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 244 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 285))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 243 285 (Eq.refl Bool.true) (allA_succ_of_gcd 42 243 285 3 14 81 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 243 285
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 243 285 (Polychromatic418967fa.accept_16_8_3_13_1_7295 40 243 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 243 285 3 13 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 243 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 38
  243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 243 285
  (Polychromatic418967fa.accept_10_7_3_5_1_301 37 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 243 285 3 12 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 243 285 (Polychromatic418967fa.accept_11_2_1_10_1_196 35 243 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 243 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 243 285 3 11 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 243 285 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 243 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 243 285 (Polychromatic418967fa.accept_11_9_1_10_1_920
  31 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 243 285 3 10 81 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 243 285
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 243 285 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 243 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 243 285 3 9 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 243 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 26
  243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 243 285
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 243 285 3 8 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 243 285 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 243 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 243 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 243 285 3 7 81 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 243 285
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 243 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 243 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 243 285 3 6 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 243 285 (Polychromatic418967fa.accept_10_7_3_5_1_301
  17 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 285
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 243 285 3 5 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 243 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 243 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 243 285 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 243
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 243 285 3 4 81 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 243 285
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 243 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 243 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 243 285 3 3 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 243 285 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 243 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 285
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 243 285 3 2 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 243 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 243 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 285 (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 243
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 243 285 3 1 81 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 243 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 243 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 243 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 243 285))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 242 285
  (Eq.refl Bool.true) (allA_succ_of_accept 43 242 285 (accept_3_4 43 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 242 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 242 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 242 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 242 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 242 285 (accept_3_4 40 242 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 242 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 242 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 242 285 (accept_3_4 37 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 242 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 242 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 242 285 (accept_3_4 34 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 242 285 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 242 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 242 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 242 285 (accept_3_4 31 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 242 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 242 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 242 285 (accept_3_4 28 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 242 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 242 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 242 285
  (Polychromatic418967fa.accept_17_9_4_13_1_3057 26 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 242 285 (accept_3_4 25 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 242 285 (Polychromatic418967fa.accept_20_4_2_5_1_4607 24 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 242 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 242 285 (accept_3_4 22 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 242 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 242 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 242 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 242 285 (accept_3_4 19 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 242 285 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 242 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 242 285 (accept_3_4 16 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 242 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 242 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 242 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 242 285 (accept_3_4 13 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 242 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 242 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 242 285 (accept_3_4 10 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 242 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 242 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 242 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 242 285 (accept_3_4 7 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  242 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 242 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 242 285 (accept_3_4 4 242 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 242 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 242 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 242 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 242 285 (accept_3_4 1 242 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  285))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_285_segment_003)))))))))))))))))))))))))))))))))))))))))))


