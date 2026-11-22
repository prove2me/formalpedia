-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch287
-- name    : Polychromatic418967fa_Branch287
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:35:17.602499+00:00
-- url     : https://prove2.me/theorems/7c06c6fa-fa6d-4045-8250-d677dd1edbd7
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch287_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_287 : allB 287 287 :=
  allB_succ' 2 286 287 (Eq.refl Bool.true) (allA_of_3_0 2 286 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  285 287 (Eq.refl Bool.true) (allA_succ_of_accept 2 285 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 285 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 285 287 (accept_3_2 1 285 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 285 287))) (allB_succ' 4 284 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 284 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 284 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 284 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 284 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 284 287 (accept_3_2 1 284 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 284 287)))) (allB_succ' 5 283 287 (Eq.refl Bool.true) (allA_of_3_0
  5 283 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 282 287 (Eq.refl Bool.true) (allA_succ_of_accept 5
  282 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 282 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 282 287 (accept_3_2 4 282 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 282 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 282 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 282 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 282 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 282 287 (accept_3_2 1 282 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 282 287)))))) (allB_succ' 7 281 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 281 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 281 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 281 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 281 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 281 287 (accept_3_2 4 281 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 281 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  281 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 281 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 281 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 281 287 (accept_3_2 1 281 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 281 287)))))))
  (allB_succ' 8 280 287 (Eq.refl Bool.true) (allA_of_3_0 8 280 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 279 287 (Eq.refl Bool.true) (allA_succ_of_accept 8 279 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 279 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 279 287 (accept_3_2 7 279 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 279 287 (Polychromatic418967fa.accept_14_6_13_7_1_2015
  6 279 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 279 287
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 279 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 279 287 (accept_3_2 4 279 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  279 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 279 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 279 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 279 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 279 287 (accept_3_2 1 279 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 279 287))))))))) (allB_succ' 10 278 287 (Eq.refl Bool.true) (allA_succ_of_accept 9 278
  287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 278 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 278 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 278 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 278 287 (accept_3_2 7 278 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 278 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 278 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 278 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  278 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 278 287 (accept_3_2 4 278
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 278 287 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 278 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 278 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 2 278 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 278 287 (accept_3_2 1 278 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 278
  287)))))))))) (allB_succ' 11 277 287 (Eq.refl Bool.true) (allA_of_3_0 11 277 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 276 287 (Eq.refl Bool.true) (allA_succ_of_accept 11 276 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 276 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 276 287 (accept_3_2 10 276 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  276 287 (Polychromatic418967fa.accept_20_9_16_7_1_1129 9 276 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 276 287 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 276 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 276 287 (accept_3_2 7 276 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 276 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 276 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 276 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 276 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 276 287 (accept_3_2 4 276 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  276 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 276 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 276 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 276 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 276 287 (accept_3_2 1 276 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 276 287)))))))))))) (allB_succ' 13 275 287 (Eq.refl Bool.true) (allA_succ_of_accept 12
  275 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 275 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 275 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 275 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 275 287 (accept_3_2 10 275 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 275 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 275 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 275 287
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 275 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 275 287 (accept_3_2 7 275 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  275 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 275 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 275 287 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 275 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 275 287 (accept_3_2 4 275 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 275 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 275 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 275 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 275 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 275 287 (accept_3_2 1 275 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 275
  287))))))))))))) (allB_succ' 14 274 287 (Eq.refl Bool.true) (allA_of_3_0 14 274 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 273 287 (Eq.refl Bool.true) (allA_succ_of_gcd 14 273 287 7 2 39 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 273 287 (accept_3_2 13 273 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 273 287
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 273 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 273 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 273 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 273 287 (accept_3_2 10 273 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 273 287 (Polychromatic418967fa.accept_17_9_1_15_1_3156 9 273 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 273 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 273 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 273 287 7 1 39 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 273 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 273 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 273 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 273 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 273 287 (accept_3_2 4 273 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 273 287 (Polychromatic418967fa.accept_12_3_9_11_1_231
  3 273 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 273 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 273 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 273 287 (accept_3_2 1 273 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 273
  287))))))))))))))) (allB_succ' 16 272 287 (Eq.refl Bool.true) (allA_succ_of_accept 15 272 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 272 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 272 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 272 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 272 287 (accept_3_2 13 272 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 272 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 272 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 272 287
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 272 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 272 287 (accept_3_2 10 272 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 272 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 272 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 272 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 272
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 272 287 (accept_3_2 7 272 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 272 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  272 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 272 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 272 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 272 287 (accept_3_2 4 272 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  272 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 272 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 272 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 272 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 272 287 (accept_3_2 1 272 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 272 287)))))))))))))))) (allB_succ' 17 271 287 (Eq.refl Bool.true) (allA_of_3_0 17 271
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 270 287 (Eq.refl Bool.true) (allA_succ_of_accept 17 270
  287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 270 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 270 287 (accept_3_2 16 270 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 270 287 (Polychromatic418967fa.accept_20_15_10_7_1_7878 15 270 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 270 287 (Polychromatic418967fa.accept_19_14_4_2_1_2840 14 270 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 270 287 (accept_3_2 13 270 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 270 287 (Polychromatic418967fa.accept_19_12_4_2_1_4121 12 270
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 270 287
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 270 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 270 287 (accept_3_2 10 270 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 270 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 270 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 270 287 (Polychromatic418967fa.accept_20_8_10_7_1_6291 8 270
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 270 287 (accept_3_2 7 270 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 270 287 (Polychromatic418967fa.accept_19_6_4_2_1_1726
  6 270 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 270 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 270 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 270 287 (accept_3_2 4 270 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  270 287 (Polychromatic418967fa.accept_14_3_4_7_1_175 3 270 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 270 287 (Polychromatic418967fa.accept_22_2_6_1_1_17651 2 270 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 270 287 (accept_3_2 1 270 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 270 287)))))))))))))))))) (allB_succ' 19 269 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 269 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 269 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 269 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 269
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 269 287 (accept_3_2 16 269
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 269 287
  (Polychromatic418967fa.accept_13_2_9_1_1_67 15 269 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 269 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 269 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 269 287 (accept_3_2 13 269 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 269 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 269 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 269 287
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 269 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 269 287 (accept_3_2 10 269 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  269 287 (Polychromatic418967fa.accept_21_9_17_14_1_603 9 269 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 269 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 269 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 269 287 (accept_3_2 7 269 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 269 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 269 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 269 287
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 269 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 269 287 (accept_3_2 4 269 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  269 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 3 269 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 269 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 269 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 269 287 (accept_3_2 1 269 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 269 287))))))))))))))))))) (allB_succ' 20 268 287 (Eq.refl Bool.true) (allA_of_3_0 20
  268 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 267 287 (Eq.refl Bool.true) (allA_succ_of_accept 20
  267 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 267 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 267 287 (accept_3_2 19 267 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 267 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 267 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 267 287 (Polychromatic418967fa.accept_16_1_11_15_1_498 17 267
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 267 287 (accept_3_2 16 267
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 267 287
  (Polychromatic418967fa.accept_19_15_1_2_1_6894 15 267 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 267 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 267 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 267 287 (accept_3_2 13 267 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 267 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 267 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 267 287 (Polychromatic418967fa.accept_9_2_6_8_1_321
  11 267 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 267 287 (accept_3_2 10
  267 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 267 287
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 267 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 267 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 267 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 267 287 (accept_3_2 7 267 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 267 287 (Polychromatic418967fa.accept_13_6_7_1_1_335 6 267 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 267 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5
  267 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 267 287 (accept_3_2 4 267
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 267 287
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 267 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 267 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 267 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 287 (accept_3_2 1 267 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 267 287))))))))))))))))))))) (allB_succ' 22 266 287 (Eq.refl Bool.true) (allA_succ_of_gcd 21 266
  287 7 3 38 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  266 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 266 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 266 287 (accept_3_2 19 266 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 266 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 266 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 266 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 266 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 266 287 (accept_3_2 16 266 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 266 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  266 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 266 287 7 2 38 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 266 287 (accept_3_2 13
  266 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 266 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 266 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 266 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 266 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 266 287 (accept_3_2 10 266 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 266 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 266 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 266 287 (Polychromatic418967fa.accept_12_8_2_11_1_246
  8 266 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 266 287 7 1 38 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 266 287
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 266 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 266 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 266 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 266 287 (accept_3_2 4 266 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 266 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 266 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 266 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2
  266 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 266 287 (accept_3_2 1 266
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 266 287)))))))))))))))))))))) (allB_succ' 23 265 287 (Eq.refl
  Bool.true) (allA_of_3_0 23 265 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 264 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 264 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 264 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 264 287 (accept_3_2 22 264 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 264 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 264 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 264 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 264 287 (accept_3_2 19 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 264 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 264 287 (Polychromatic418967fa.accept_16_1_8_15_1_1945 17 264 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 264 287 (accept_3_2 16 264 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 264 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 264 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 264 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 264 287 (accept_3_2 13 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 264 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 264 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 264 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 264 287 (accept_3_2 10 264 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 264 287 (Polychromatic418967fa.accept_14_9_12_7_1_597 9 264 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 264 287
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 264 287 (accept_3_2 7 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  264 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 264 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 264 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 264 287 (accept_3_2 4 264 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 264 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 264 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 264 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 264 287 (accept_3_2 1 264 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 264
  287)))))))))))))))))))))))) (allB_succ' 25 263 287 (Eq.refl Bool.true) (allA_succ_of_accept 24 263 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 263 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 263 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 263 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 263 287 (accept_3_2 22 263 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 263 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 263 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 263 287 (Polychromatic418967fa.accept_11_9_10_1_1_581
  20 263 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 263 287 (accept_3_2 19
  263 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 263 287
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 263 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 263 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 263 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 263 287 (accept_3_2 16 263 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 263 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 263 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 263 287 (Polychromatic418967fa.accept_9_5_2_8_1_109
  14 263 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 263 287 (accept_3_2 13
  263 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 263 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 263 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 263 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 263 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 263 287 (accept_3_2 10 263 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 263 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 263 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 263 287 (Polychromatic418967fa.accept_16_8_7_15_1_6339
  8 263 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 263 287 (accept_3_2 7
  263 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 263 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 6 263 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 263 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 263 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 263 287 (accept_3_2 4 263 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 263 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 263 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 263 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  2 263 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 263 287 (accept_3_2 1
  263 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 263 287))))))))))))))))))))))))) (allB_succ' 26 262 287
  (Eq.refl Bool.true) (allA_of_3_0 26 262 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 261 287 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 261 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 261 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 261 287 (accept_3_2 25 261 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 261 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 261 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 261 287
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 261 287 (accept_3_2 22 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 261 287 (Polychromatic418967fa.accept_25_21_11_12_1_17661 21 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 20 261 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 261 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 261 287 (accept_3_2 19 261 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 261 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 261 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 261 287
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 261 287 (accept_3_2 16 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 261 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 261 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 261 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 261 287 (accept_3_2 13 261 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 261 287 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 261 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 261 287
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 11 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 261 287 (accept_3_2 10 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  261 287 (Polychromatic418967fa.accept_17_9_6_15_1_5454 9 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 261 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 261 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 261 287 (accept_3_2 7 261 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 261 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 261 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 261 287
  (Polychromatic418967fa.accept_14_5_9_7_1_590 5 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 261 287 (accept_3_2 4 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  261 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 261 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 261 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 261 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 261 287 (accept_3_2 1 261 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 261 287))))))))))))))))))))))))))) (allB_succ' 28 260 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 260 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 260 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 260 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 260
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 260 287 (accept_3_2 25 260
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 260 287
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 260 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 260 287 (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 260 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 260 287 (accept_3_2 22 260 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 260 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 260 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 260 287 (Polychromatic418967fa.accept_14_6_8_7_1_589
  20 260 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 260 287 (accept_3_2 19
  260 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 260 287
  (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 260 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 260 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 260 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 260 287 (accept_3_2 16 260 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 260 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 260 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 260 287 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 260 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 260 287 (accept_3_2 13
  260 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 260 287
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 12 260 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 260 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 260 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 260 287 (accept_3_2 10 260 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 260 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 260 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 260 287 (Polychromatic418967fa.accept_16_8_4_15_1_2941
  8 260 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 260 287 (accept_3_2 7
  260 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 260 287
  (Polychromatic418967fa.accept_11_6_7_1_1_564 6 260 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 260 287 (Polychromatic418967fa.accept_16_5_4_15_1_1102 5 260 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 260 287 (accept_3_2 4 260 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 260 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 260 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 260 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  260 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 260 287 (accept_3_2 1 260
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 260 287)))))))))))))))))))))))))))) (allB_succ' 29 259 287
  (Eq.refl Bool.true) (allA_of_3_0 29 259 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 258 287 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 258 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 258 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 258 287 (accept_3_2 28 258 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 258 287 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 258 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 258 287
  (Polychromatic418967fa.accept_24_2_18_23_1_11077 26 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 258 287 (accept_3_2 25 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 258 287 (Polychromatic418967fa.accept_21_3_6_14_1_5717 24 258 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 258 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 258 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 258 287 (accept_3_2 22 258 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 258 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  258 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 258 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 258 287 (accept_3_2 19 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 258 287 (Polychromatic418967fa.accept_17_1_3_15_1_2153 18 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 258 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 258 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 258 287 (accept_3_2 16 258 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 258 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 258 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 258 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 258 287 (accept_3_2 13 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 258 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 258 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 258 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 258 287 (accept_3_2 10 258 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 258 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 258 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 258 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 258 287 (accept_3_2 7 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  258 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 258 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 258 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 258 287 (accept_3_2 4 258 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 258 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 258 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 258 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 258 287 (accept_3_2 1 258 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 258
  287)))))))))))))))))))))))))))))) (allB_succ' 31 257 287 (Eq.refl Bool.true) (allA_succ_of_accept 30 257 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 257 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 257 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 257 287 (accept_3_2 28 257 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 257 287 (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 257 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 257 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 257 287 (accept_3_2 25 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 257 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 257 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 23 257 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 257 287 (accept_3_2 22 257 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 257 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 257 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 257 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 257 287 (accept_3_2 19 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 257 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 257 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 257 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 257 287 (accept_3_2 16 257 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 257 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 257 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 257 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 257 287 (accept_3_2 13 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 257 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 257 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 257 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 257 287 (accept_3_2 10 257 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 257 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 257 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 257 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 257 287 (accept_3_2 7 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  257 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 257 287 (Polychromatic418967fa.accept_16_5_1_15_1_3922 5 257 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 257 287 (accept_3_2 4 257 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 257 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 257 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 257 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 257 287 (accept_3_2 1 257 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 257
  287))))))))))))))))))))))))))))))) (allB_succ' 32 256 287 (Eq.refl Bool.true) (allA_of_3_0 32 256 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 255 287 (Eq.refl Bool.true) (allA_succ_of_accept 32 255 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 255 287 (accept_3_2 31 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 255 287 (Polychromatic418967fa.accept_19_11_8_2_1_2847 30 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 255 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 255 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 255 287 (accept_3_2 28 255 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 255 287 (Polychromatic418967fa.accept_21_6_3_14_1_11869 27 255 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 255 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 255 287 (accept_3_2 25 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 255 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 255 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 255 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 255 287 (accept_3_2 22 255 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 255 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 255 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 255 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 255 287 (accept_3_2 19 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 255 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 255 287 (Polychromatic418967fa.accept_21_17_3_14_1_2807 17 255 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 255 287 (accept_3_2 16 255 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 255 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 255 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 255 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 255 287 (accept_3_2 13 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 255 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 255 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 255 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 255 287 (accept_3_2 10 255 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 255 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 255 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 255 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 255 287 (accept_3_2 7 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  255 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 255 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 255 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 255 287 (accept_3_2 4 255 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 255 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 255 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 255 287 (accept_3_2 1 255 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 255
  287))))))))))))))))))))))))))))))))) (allB_succ' 34 254 287 (Eq.refl Bool.true) (allA_succ_of_accept 33 254 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 254 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 254 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 254 287 (accept_3_2 31 254 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 254 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 254 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 254 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 254 287 (accept_3_2 28
  254 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 254 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 254 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 254 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 254 287 (accept_3_2 25 254 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 254 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 254 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 254 287 (Polychromatic418967fa.accept_9_5_2_8_1_109
  23 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 254 287 (accept_3_2 22
  254 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 254 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 254 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 254 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 254 287 (accept_3_2 19 254 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 254 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 254 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 254 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 254 287 (accept_3_2 16 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 254 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 254 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 254 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 254 287 (accept_3_2 13 254 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 254 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 254 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 254 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 254 287 (accept_3_2 10 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  254 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 254 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 254 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 254 287 (accept_3_2 7 254 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 254 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 254 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 254 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 254 287 (accept_3_2 4 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  254 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 254 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 254 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 254 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 254 287 (accept_3_2 1 254 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 254 287)))))))))))))))))))))))))))))))))) (allB_succ' 35 253 287 (Eq.refl Bool.true)
  (allA_of_3_0 35 253 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 252 287 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 252 287 7 5 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 252 287 (accept_3_2 34 252 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 252 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 252 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 252 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 32 252 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 252 287 (accept_3_2 31 252 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 252 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 30 252
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 252 287
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 252 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 252 287 7 4 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 252 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 252 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 252 287 (Polychromatic418967fa.accept_19_7_5_2_1_2842 26 252
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 252 287 (accept_3_2 25 252
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 252 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 252 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 252 287 (Polychromatic418967fa.accept_17_6_14_15_1_5505 23 252 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 252 287 (accept_3_2 22 252 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 252 287 7 3 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 252 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 252
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 252 287 (accept_3_2 19 252
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 252 287
  (Polychromatic418967fa.accept_15_3_12_2_1_507 18 252 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 252 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 252 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 252 287 (accept_3_2 16 252 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 252 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 252 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 252 287 7 2 36 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 252 287 (accept_3_2 13 252 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 252 287
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 252 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 252 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 252 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 252 287 (accept_3_2 10 252 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 252 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 252 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 252 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  8 252 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 252 287 7 1 36 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 252 287
  (Polychromatic418967fa.accept_13_6_5_1_1_834 6 252 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 252 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 252 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 252 287 (accept_3_2 4 252 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 252 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 252 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 252 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  2 252 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 252 287 (accept_3_2 1
  252 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252 287)))))))))))))))))))))))))))))))))))) (allB_succ' 37
  251 287 (Eq.refl Bool.true) (allA_succ_of_accept 36 251 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 251 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 251 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 251 287 (accept_3_2 34 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 251 287 (Polychromatic418967fa.accept_16_1_11_15_1_498 33 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 251 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 251 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 251 287 (accept_3_2 31 251 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 251 287 (Polychromatic418967fa.accept_19_11_4_2_1_1700 30 251
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 251 287
  (Polychromatic418967fa.accept_13_3_4_1_1_363 29 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 251 287 (accept_3_2 28 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 251 287 (Polychromatic418967fa.accept_21_6_20_14_1_8837 27 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 251 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 26 251 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 251 287 (accept_3_2 25 251 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 251 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 251
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 251 287
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 251 287 (accept_3_2 22 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 251 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 251 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 251 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 251 287 (accept_3_2 19 251 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 251 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 251 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 251 287
  (Polychromatic418967fa.accept_16_1_11_15_1_498 17 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 251 287 (accept_3_2 16 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 251 287 (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 251 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 251 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 251 287 (accept_3_2 13 251 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 251 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 251 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 251 287
  (Polychromatic418967fa.accept_17_11_13_15_1_2140 11 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 251 287 (accept_3_2 10 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 251 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 251 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 251 287 (Polychromatic418967fa.accept_14_8_13_7_1_2798 8 251
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 251 287 (accept_3_2 7 251 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 251 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 6
  251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 251 287
  (Polychromatic418967fa.accept_13_5_4_1_1_364 5 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 251 287 (accept_3_2 4 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  251 287 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 251 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 251 287 (Polychromatic418967fa.accept_17_2_13_15_1_4349 2 251 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 251 287 (accept_3_2 1 251 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 251 287))))))))))))))))))))))))))))))))))))) (allB_succ' 38 250 287 (Eq.refl
  Bool.true) (allA_of_3_0 38 250 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 249 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 249 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 249 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 249 287 (accept_3_2 37 249 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 249 287 (Polychromatic418967fa.accept_20_16_9_7_1_3402 36 249 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 249 287
  (Polychromatic418967fa.accept_13_9_2_1_1_813 35 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 249 287 (accept_3_2 34 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 249 287 (Polychromatic418967fa.accept_17_16_11_15_1_4353 33 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 32 249 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 249 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 249 287 (accept_3_2 31 249 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 249 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 249 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 249 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 249 287 (accept_3_2 28 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 249 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 249 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 249 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 249 287 (accept_3_2 25 249 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 249 287 (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 249 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 249 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 249 287 (accept_3_2 22 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 249 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 249 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 249 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 249 287 (accept_3_2 19 249 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 249 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 249 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 249 287
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 249 287 (accept_3_2 16 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 249 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 249 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 249 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 287 (accept_3_2 13 249 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 249 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 249 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 249 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 249 287 (accept_3_2 10 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  249 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 249 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 249 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 287 (accept_3_2 7 249 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 249 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 249 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 249 287 (accept_3_2 4 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  249 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 249 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 249 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 249 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 287 (accept_3_2 1 249 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 249 287))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 248 287 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 248 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 248 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 248 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 38
  248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 248 287 (accept_3_2 37
  248 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 248 287
  (Polychromatic418967fa.accept_15_6_8_2_1_104 36 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 248 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 248 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 248 287 (accept_3_2 34 248 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 248 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 248 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 248 287
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 32 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 248 287 (accept_3_2 31 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 248 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 248 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 248 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 248 287 (accept_3_2 28 248 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 248 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 248 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 248 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 248 287 (accept_3_2 25 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 248 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 248 287 (Polychromatic418967fa.accept_16_7_8_15_1_6327 23 248 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 248 287 (accept_3_2 22 248 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 248 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 248 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 248 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 248 287 (accept_3_2 19 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 248 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 248 287 (Polychromatic418967fa.accept_14_3_10_7_1_3773 17 248 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 248 287 (accept_3_2 16 248 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 248 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 248 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 248 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 248 287 (accept_3_2 13 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 248 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 248 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 248 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 248 287 (accept_3_2 10 248 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 248 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 248 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 248 287
  (Polychromatic418967fa.accept_17_8_10_15_1_9328 8 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 248 287 (accept_3_2 7 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  248 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 248 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 248 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 248 287 (accept_3_2 4 248 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 248 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 248 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 248 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 248 287 (accept_3_2 1 248 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248
  287)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 247 287 (Eq.refl Bool.true) (allA_of_3_0 41 247 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 246 287 (Eq.refl Bool.true) (allA_succ_of_gcd 41 246 287 41 1
  6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 40 246 287
  (accept_3_2 40 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 246 287
  (Polychromatic418967fa.accept_16_7_6_15_1_495 39 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 246 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 246 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 246 287 (accept_3_2 37 246 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 246 287 (Polychromatic418967fa.accept_20_16_6_7_1_10779 36 246 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 246 287
  (Polychromatic418967fa.accept_19_16_18_2_1_6934 35 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 246 287 (accept_3_2 34 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 246 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 246 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 246 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 246 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 246 287 (accept_3_2 31 246 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 246 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000
  30 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 246 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 246 287 (accept_3_2 28 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 246 287 (Polychromatic418967fa.accept_14_13_8_7_1_1224 27 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 246 287 (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 246 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 246 287 (accept_3_2 25 246 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 246 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 246 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 246 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 246 287 (accept_3_2 22 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 246 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 246 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 246 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 246 287 (accept_3_2 19 246 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 246 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 246 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 246 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 246 287 (accept_3_2 16 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 246 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 246 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 246 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 246 287 (accept_3_2 13 246 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 246 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 246 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 246 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 246 287 (accept_3_2 10 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  246 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 246 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 246 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 246 287 (accept_3_2 7 246 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 246 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 246 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 246 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 246 287 (accept_3_2 4 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  246 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 246 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 246 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 246 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 287 (accept_3_2 1 246 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 246 287)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 245 287 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 245 287 7 6 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 245 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 245 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 245 287 (accept_3_2 40 245 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 245 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 245 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 245 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 245 287 (accept_3_2 37 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 245 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 245 287 7 5 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 245 287 (accept_3_2 34 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 245 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 245 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 245 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 245 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 245 287 (accept_3_2 31 245 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 245 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 245 287
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 29 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 245 287 7 4 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 245 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 245 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 245 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 245 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 245 287 (accept_3_2 25 245 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 245 287 (Polychromatic418967fa.accept_9_6_2_8_1_592
  24 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 245 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 245 287 (accept_3_2 22 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  245 287 7 3 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 245 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 245 287 (accept_3_2 19 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 245 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 245 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 245 287 (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 245
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 245 287 (accept_3_2 16 245
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 245 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 245 287 7 2 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 245 287 (accept_3_2 13 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 245 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 245 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 245 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 245 287 (accept_3_2 10 245 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 245 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 245
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 245 287
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 245 287 7 1 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 245 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 245 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 245 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 245 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 245 287 (accept_3_2 4 245 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 287 (accept_3_2 1 245 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245
  287))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 244 287 (Eq.refl Bool.true) (allA_of_3_0 44 244 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 243 287 (Eq.refl Bool.true) (allA_succ_of_accept 44 243 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 243 287 (accept_3_2 43 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 243 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 243 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 41 243 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 243 287 (accept_3_2 40 243 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 243 287 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 243 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 243 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 243 287 (accept_3_2 37 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 243 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 243 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 243 287 (accept_3_2 34 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 243 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 243
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 243 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 243 287 (accept_3_2 31 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 243 287 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 243 287 (Polychromatic418967fa.accept_15_14_3_2_1_2811 29 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 243 287 (accept_3_2 28 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 243 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 243
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 243 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 243 287 (accept_3_2 25 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 243 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 243 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 287 (accept_3_2 22 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 243 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 243
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 243 287 (accept_3_2 19 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 243 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 243 287 (Polychromatic418967fa.accept_19_17_15_2_1_6887 17 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 287 (accept_3_2 16 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 243
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 243 287 (accept_3_2 13 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 243 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 243 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 287 (accept_3_2 10 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 243
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 243 287 (accept_3_2 7 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  243 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 243 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 243 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 287 (accept_3_2 4 243 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 287 (Polychromatic418967fa.accept_21_3_12_14_1_8848 3 243 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 287 (accept_3_2 1 243 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243
  287))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 242 287 (Eq.refl Bool.true) (allA_succ_of_accept 45
  242 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 242 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 242 287 (accept_3_2 43 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 242 287 (Polychromatic418967fa.accept_19_4_14_2_1_4117 42 242
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 242 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 242 287 (accept_3_2 40 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 242 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 242 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 38 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 242 287 (accept_3_2 37 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 242 287 (Polychromatic418967fa.accept_17_2_4_15_1_5451 36 242
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 242 287
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 242 287 (accept_3_2 34 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 242 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 242 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 242 287 (accept_3_2 31 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 242 287 (Polychromatic418967fa.accept_25_5_17_12_1_5193 30 242
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 242 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 242 287 (accept_3_2 28 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 242 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 242 287 (Polychromatic418967fa.accept_19_7_14_2_1_4095 26 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 242 287 (accept_3_2 25 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 242 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 242
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 242 287
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 242 287 (accept_3_2 22 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 242 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 242 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 242 287 (accept_3_2 19 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 242 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 242
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 242 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 242 287 (accept_3_2 16 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 242 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 242 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 242 287 (accept_3_2 13 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 242 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 242
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 242 287
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 242 287 (accept_3_2 10 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  242 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 242 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 242 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 242 287 (accept_3_2 7 242 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 242 287 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 242 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 242 287 (accept_3_2 4 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  242 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 242 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 242 287 (Polychromatic418967fa.accept_17_2_4_15_1_5451 2 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 242 287 (accept_3_2 1 242 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 242 287)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 241 287
  (Eq.refl Bool.true) (allA_of_3_0 47 241 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 240 287 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 240 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 240 287 (accept_3_2 46 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 240 287 (Polychromatic418967fa.accept_21_3_9_14_1_5701 45 240 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 240 287
  (Polychromatic418967fa.accept_13_5_6_1_1_822 44 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 240 287 (accept_3_2 43 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 240 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 240 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 240 287 (accept_3_2 40 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 240 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 240 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 240 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 240 287 (accept_3_2 37 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 240 287 (Polychromatic418967fa.accept_19_17_12_2_1_6880 36 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 240 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 240 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 240 287 (accept_3_2 34 240 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 240 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 33 240
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 240 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 240 287 (accept_3_2 31 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 240 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 240 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 240 287 (accept_3_2 28 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 240 287 (Polychromatic418967fa.accept_17_10_2_15_1_3179 27 240 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 240 287
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 240 287 (accept_3_2 25 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 240 287 (Polychromatic418967fa.accept_17_7_2_15_1_1255 24 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 240 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 240 287 (accept_3_2 22 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 240 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 240 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 240 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 240 287 (accept_3_2 19 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 240 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 240 287 (Polychromatic418967fa.accept_19_17_12_2_1_6880 17 240 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 240 287 (accept_3_2 16 240 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 240 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 240
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 240 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 240 287 (accept_3_2 13 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 240 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 240 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 240 287 (accept_3_2 10 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 240 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 240 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 240 287
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 240 287 (accept_3_2 7 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  240 287 (Polychromatic418967fa.accept_19_6_12_2_1_8379 6 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 240 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 240 287 (accept_3_2 4 240 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 240 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 240 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 240 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 240 287 (accept_3_2 1 240 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240
  287)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 239 287 (Eq.refl Bool.true) (allA_succ_of_accept 48
  239 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 239 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 239 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 239 287 (accept_3_2 46 239 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 239 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 45 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 239 287
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 239 287 (accept_3_2 43 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 239 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 239 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 41 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 239 287 (accept_3_2 40 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 239 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 239 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 239 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 239 287 (accept_3_2 37 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 239 287 (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 239 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 239 287 (accept_3_2 34 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 239 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 239 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 239 287
  (Polychromatic418967fa.accept_10_2_9_7_1_720 32 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 239 287 (accept_3_2 31 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 239 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 239 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 239 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 239 287 (accept_3_2 28 239 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 239 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 239 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 239 287
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 239 287 (accept_3_2 25 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 239 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 239 287 (Polychromatic418967fa.accept_19_4_11_2_1_11111 23 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 239 287 (accept_3_2 22 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 239 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 239 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 239 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 239 287 (accept_3_2 19 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 239 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 239 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 239 287 (accept_3_2 16 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 239 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 239 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 239 287
  (Polychromatic418967fa.accept_26_14_5_1_1_10547 14 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 239 287 (accept_3_2 13 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 239 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 239 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 239 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 239 287 (accept_3_2 10 239 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 239 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382
  9 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 239 287
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 239 287 (accept_3_2 7 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  239 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 239 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 287 (accept_3_2 4 239 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 239 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 239 287 (accept_3_2 1 239 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239
  287))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 238 287 (Eq.refl Bool.true) (allA_of_3_0 50 238
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 237 287 (Eq.refl Bool.true) (allA_succ_of_accept 50 237
  287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 237 287 (accept_3_2 49 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 237 287 (Polychromatic418967fa.accept_14_6_13_7_1_2015 48 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 237 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 237 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 237 287 (accept_3_2 46 237 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 237 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 237 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 237 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 237 287 (accept_3_2 43 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 237 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 237 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 237 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 237 287 (accept_3_2 40 237 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 237 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 237 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 237 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 237 287 (accept_3_2 37 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 237 287 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 237 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 237 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 237 287 (accept_3_2 34 237 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 237 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 237 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 237 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 237 287 (accept_3_2 31 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 237 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 237 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 237 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 237 287 (accept_3_2 28 237 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 237 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 237 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 237 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 237 287 (accept_3_2 25 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 237 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 237 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 237 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 287 (accept_3_2 22 237 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 237 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 237 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 237 287 (accept_3_2 19 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 237 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 237 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 237 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 287 (accept_3_2 16 237 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 237 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 237 287 (accept_3_2 13 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 237 287 (Polychromatic418967fa.accept_16_12_13_15_1_1966 12 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 237 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 287 (accept_3_2 10 237 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 287 (Polychromatic418967fa.accept_20_9_17_7_1_4748 9 237
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 287 (accept_3_2 7 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  237 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 237 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 237 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 287 (accept_3_2 4 237 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 237 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 287 (accept_3_2 1 237 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237
  287))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 236 287 (Eq.refl Bool.true) (allA_succ_of_accept
  51 236 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 236 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 236 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 236 287 (accept_3_2 49 236 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 236 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 236 287
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 47 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 236 287 (accept_3_2 46 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 236 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 236 287 (Polychromatic418967fa.accept_14_2_12_7_1_617 44 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 236 287 (accept_3_2 43 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 236 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 236 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 236 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 236 287 (accept_3_2 40 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 236 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 236 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 236 287 (accept_3_2 37 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 236 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 36 236
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 236 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 236 287 (accept_3_2 34 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 236 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 236 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 236 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 236 287 (accept_3_2 31 236 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 236 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 236 287
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 236 287 (accept_3_2 28 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 236 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 236 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 236 287 (accept_3_2 25 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 236 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 236 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 236 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 236 287 (accept_3_2 22 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 236 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 236 287 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 236 287 (accept_3_2 19 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 236 287 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 236
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 236 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 236 287 (accept_3_2 16 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 236 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 236 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 236 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 236 287 (accept_3_2 13 236 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 236 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 236 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 236 287 (accept_3_2 10 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  236 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 236 287 (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 236 287 (accept_3_2 7 236 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 236 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 236 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 236 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 236 287 (accept_3_2 4 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  236 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 236 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 236 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 236 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 236 287 (accept_3_2 1 236 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 236 287)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 235 287
  (Eq.refl Bool.true) (allA_of_3_0 53 235 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 234 287 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 234 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 234 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 234 287 (accept_3_2 52 234 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 234 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 234 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 234 287
  (Polychromatic418967fa.accept_19_12_6_2_1_5424 50 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 234 287 (accept_3_2 49 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 234 287 (Polychromatic418967fa.accept_19_10_6_2_1_6907 48 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 234 287 (Polychromatic418967fa.accept_22_3_14_1_1_17660 47 234 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 234 287 (accept_3_2 46 234 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 234 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 234 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 234 287
  (Polychromatic418967fa.accept_21_2_3_14_1_5690 44 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 234 287 (accept_3_2 43 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 234 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 234 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 234 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 234 287 (accept_3_2 40 234 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 234 287 (Polychromatic418967fa.accept_14_11_10_7_1_1948 39 234 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 234 287
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 38 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 234 287 (accept_3_2 37 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 234 287 (Polychromatic418967fa.accept_17_2_13_15_1_4349 36 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 234 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 234 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 234 287 (accept_3_2 34 234 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 234 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 234 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 234 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 234 287 (accept_3_2 31 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 234 287 (Polychromatic418967fa.accept_16_14_10_15_1_3969 30 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 234 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 234 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 234 287 (accept_3_2 28 234 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 234 287 (Polychromatic418967fa.accept_16_11_10_15_1_6301 27
  234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 234 287
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 234 287 (accept_3_2 25 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 234 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 234 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 234 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 234 287 (accept_3_2 22 234 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 234 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 234 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 234 287
  (Polychromatic418967fa.accept_19_1_6_2_1_8341 20 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 234 287 (accept_3_2 19 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 234 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 234 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 234 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 234 287 (accept_3_2 16 234 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 234 287 (Polychromatic418967fa.accept_19_15_6_2_1_6865 15 234 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 234 287
  (Polychromatic418967fa.accept_16_14_10_15_1_3969 14 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 234 287 (accept_3_2 13 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 234 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 234 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 234
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 287 (accept_3_2 10 234
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 234 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  9 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 234 287
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 234 287 (accept_3_2 7 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  234 287 (Polychromatic418967fa.accept_21_6_3_14_1_11869 6 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 234 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 234 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 234 287 (accept_3_2 4 234 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 234 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 234 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 234 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 234 287 (accept_3_2 1 234 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 233 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 233 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 233 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 233 287 (Polychromatic418967fa.accept_21_11_2_14_1_7225 53 233
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 233 287 (accept_3_2 52 233
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 233 287
  (Polychromatic418967fa.accept_15_6_8_2_1_104 51 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 233 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 233 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 233 287 (accept_3_2 49 233 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 233 287 (Polychromatic418967fa.accept_17_14_12_15_1_5558 48 233 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 233 287
  (Polychromatic418967fa.accept_11_3_2_1_1_994 47 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 233 287 (accept_3_2 46 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 233 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 233 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 233 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 233 287 (accept_3_2 43 233 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 233 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 233 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 233 287
  (Polychromatic418967fa.accept_13_2_12_1_1_343 41 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 233 287 (accept_3_2 40 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 233 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 233 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 233 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 233 287 (accept_3_2 37 233 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 233 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 233 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 233 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 233 287 (accept_3_2 34 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 233 287 (Polychromatic418967fa.accept_14_5_9_7_1_590 33 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 233 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 233 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 233 287 (accept_3_2 31 233 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 233 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 233 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 233 287
  (Polychromatic418967fa.accept_19_10_5_2_1_9784 29 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 233 287 (accept_3_2 28 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 233 287 (Polychromatic418967fa.accept_19_8_5_2_1_4105 27 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 233 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 233 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 233 287 (accept_3_2 25 233 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 233 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 233 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 233 287
  (Polychromatic418967fa.accept_19_4_5_2_1_8374 23 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 233 287 (accept_3_2 22 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 233 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 233 287 (Polychromatic418967fa.accept_17_3_12_15_1_1203 20 233 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 287 (accept_3_2 19 233 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 233 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 233 287
  (Polychromatic418967fa.accept_19_17_5_2_1_2843 17 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 233 287 (accept_3_2 16 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 233 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 233 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 233 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 287 (accept_3_2 13 233 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 287 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 233 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 233 287
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 233 287 (accept_3_2 10 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 233 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 233 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 233
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 287 (accept_3_2 7 233 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 233 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 233 287 (accept_3_2 4 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  233 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 233 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 233 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 233 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 287 (accept_3_2 1 233 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 233 287))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 232 287
  (Eq.refl Bool.true) (allA_of_3_0 56 232 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 231 287 (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 231 287 7 8 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 231 287 (accept_3_2 55 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 231 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 231 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 231 287 (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 231
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 231 287 (accept_3_2 52 231
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 231 287
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 51 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 231 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 231 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 231 287 7 7 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 231 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48
  231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 231 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 231 287 (accept_3_2 46 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 231 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 231 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 231 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 231 287 (accept_3_2 43 231 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 231 287 7 6 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 231 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 231 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 231 287 (accept_3_2 40 231 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 231 287 (Polychromatic418967fa.accept_9_3_6_8_1_308
  39 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 231 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 231 287 (accept_3_2 37 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 231 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 231 287 7 5 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 231 287 (accept_3_2 34 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 231 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 231 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 231 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 231 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 231 287 (accept_3_2 31 231 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 231 287 (Polychromatic418967fa.accept_9_3_6_8_1_308
  30 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 231 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 231 287 7 4 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 231 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 231 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 231 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 231 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 231 287 (accept_3_2 25 231 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 231 287 (Polychromatic418967fa.accept_10_4_1_7_1_371
  24 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 231 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 231 287 (accept_3_2 22 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  231 287 7 3 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 231 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 231 287 (accept_3_2 19 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 231 287 (Polychromatic418967fa.accept_19_18_3_2_1_6939 18 231 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 231 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 231
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 287 (accept_3_2 16 231
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 287
  (Polychromatic418967fa.accept_22_15_11_1_1_6777 15 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 231 287 7 2 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 231 287 (accept_3_2 13 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 231 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 231 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 231 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 287 (accept_3_2 10 231 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097
  9 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 231 287 7 1 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 231 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 231 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 231 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 287 (accept_3_2 4 231 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 287 (accept_3_2 1 231 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 230 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 230 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 230 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 230 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 230 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 230 287 (accept_3_2 55 230 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 230 287 (Polychromatic418967fa.accept_13_2_9_1_1_67
  54 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 230 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 230 287 (accept_3_2 52 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 230 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 230 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 50 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 230 287 (accept_3_2 49 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 230 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 230 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 230 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 230 287 (accept_3_2 46 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 230 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 230 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 230 287 (accept_3_2 43 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 230 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 230 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 230 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 230 287 (accept_3_2 40 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 230 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 230 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 230 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 230 287 (accept_3_2 37 230 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 230 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 230 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 230 287
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 230 287 (accept_3_2 34 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 230 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 230 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 230 287 (accept_3_2 31 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 230 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 230 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 230 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 230 287 (accept_3_2 28 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 230 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 230 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 230 287 (accept_3_2 25 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 230 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 230 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 230 287
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 230 287 (accept_3_2 22 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 230 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 230 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 230 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 230 287 (accept_3_2 19 230 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 230 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 230 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 230 287 (accept_3_2 16 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 230 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 230 287 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 230 287 (accept_3_2 13 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 230 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 230 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 230 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 230 287 (accept_3_2 10 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  230 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 230 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 230 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 230 287 (accept_3_2 7 230 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 230 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 230 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 230 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 230 287 (accept_3_2 4 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  230 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 230 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 230 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 230 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 230 287 (accept_3_2 1 230 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 230 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 229
  287 (Eq.refl Bool.true) (allA_of_3_0 59 229 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 228 287
  (Eq.refl Bool.true) (allA_succ_of_accept 59 228 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 228 287 (accept_3_2 58 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 228 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 57 228
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 228 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 228 287 (accept_3_2 55 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 228 287 (Polychromatic418967fa.accept_21_12_18_14_1_8854 54 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 228 287 (Polychromatic418967fa.accept_14_11_4_7_1_609 53 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 228 287 (accept_3_2 52 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 228 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 228 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 228 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 228 287 (accept_3_2 49 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 228 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 228 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 228 287 (accept_3_2 46 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 228 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 228 287
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 44 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 228 287 (accept_3_2 43 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 228 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 228 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 228 287 (accept_3_2 40 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 228 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 228 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 228 287 (accept_3_2 37 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 228 287 (Polychromatic418967fa.accept_17_2_7_15_1_5525 36 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 228 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 228 287 (accept_3_2 34 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 228 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 228 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 228 287 (accept_3_2 31 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 228 287 (Polychromatic418967fa.accept_16_14_4_15_1_3944 30 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 228 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 228 287 (accept_3_2 28 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 228 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 228 287
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 228 287 (accept_3_2 25 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 228 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 228 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 228 287 (accept_3_2 22 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 228 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 228 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 228 287 (accept_3_2 19 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 228 287 (Polychromatic418967fa.accept_22_18_8_1_1_11637 18 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 228 287 (Polychromatic418967fa.accept_14_3_4_7_1_175 17 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 287 (accept_3_2 16 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 228 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 228 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 228 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 228 287 (accept_3_2 13 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 228 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 228 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 287 (accept_3_2 10 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 228 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 228 287
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 228 287 (accept_3_2 7 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  228 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 228 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 228 287 (accept_3_2 4 228 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 228 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 228 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 228 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 228 287 (accept_3_2 1 228 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 227 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 227 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 227 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 227 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 227 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 227 287 (accept_3_2 58 227 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 227 287 (Polychromatic418967fa.accept_9_3_2_8_1_108
  57 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 227 287
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 56 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 227 287 (accept_3_2 55 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 227 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 227 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 227 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 53 227
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 227 287 (accept_3_2 52 227
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 227 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 227 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 227 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 227 287 (accept_3_2 49 227 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 227 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 227 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808
  47 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 227 287 (accept_3_2 46
  227 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 227 287
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 45 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 227 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 227 287 (accept_3_2 43 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 227 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 227 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 227 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 227 287 (accept_3_2 40 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 227 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 227 287 (Polychromatic418967fa.accept_14_10_3_7_1_1975 38 227 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 227 287 (accept_3_2 37 227 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 227 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 227 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 227 287
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 227 287 (accept_3_2 34 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 227 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 227 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 227 287 (accept_3_2 31 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 227 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 227 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 227 287
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 227 287 (accept_3_2 28 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 227 287 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 227 287 (Polychromatic418967fa.accept_17_9_6_15_1_5454 26 227 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 227 287 (accept_3_2 25 227 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 227 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 227 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 227 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 227 287 (accept_3_2 22 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 227 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 227 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 287 (accept_3_2 19 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 227 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 287
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 227 287 (accept_3_2 16 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 227 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 227 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 287 (accept_3_2 13 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 227 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 287
  (Polychromatic418967fa.accept_14_11_3_7_1_604 11 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 287 (accept_3_2 10 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 287 (accept_3_2 7 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 227 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 287 (accept_3_2 4 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 227 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 287 (accept_3_2 1 227 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 226
  287 (Eq.refl Bool.true) (allA_of_3_0 62 226 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 225 287
  (Eq.refl Bool.true) (allA_succ_of_accept 62 225 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 225 287 (accept_3_2 61 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 225 287 (Polychromatic418967fa.accept_19_3_16_2_1_6837 60 225
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 225 287
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 59 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 225 287 (accept_3_2 58 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 225 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 57 225 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 225 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 225 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 225 287 (accept_3_2 55 225 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 225 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 225 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 225 287 (accept_3_2 52 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 225 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 225 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 225 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 225 287 (accept_3_2 49 225 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 225 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 225 287
  (Polychromatic418967fa.accept_21_5_15_14_1_2787 47 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 225 287 (accept_3_2 46 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 225 287 (Polychromatic418967fa.accept_17_11_4_15_1_3150 45 225 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 225 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44
  225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 225 287 (accept_3_2 43
  225 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 225 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 225 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 41 225 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 225 287 (accept_3_2 40 225 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 225 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 225 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 225 287 (accept_3_2 37 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 225 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 225 287 (Polychromatic418967fa.accept_20_15_5_7_1_4791 35 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 225 287 (accept_3_2 34 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 225
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 225 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 225 287 (accept_3_2 31 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 225 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 225 287 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 287 (accept_3_2 28 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 225
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 225 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 225 287 (accept_3_2 25 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 225 287 (Polychromatic418967fa.accept_16_8_1_15_1_1982 24 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 225 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 287 (accept_3_2 22 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 287 (Polychromatic418967fa.accept_16_5_1_15_1_3922 21 225
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 225 287 (accept_3_2 19 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 225 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 225 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 287 (accept_3_2 16 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 225
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 287 (accept_3_2 13 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 225 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 225 287 (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 287 (accept_3_2 10 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 287 (Polychromatic418967fa.accept_20_9_5_7_1_6336 9 225 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 287 (accept_3_2 7 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  225 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 225 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 5 225 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 287 (accept_3_2 4 225 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 225 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 287 (accept_3_2 1 225 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 224 287 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 224 287 7 9 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 224 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 224 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 224 287 (accept_3_2 61 224 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 224 287 (Polychromatic418967fa.accept_24_12_8_23_1_17659 60 224 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 224 287
  (Polychromatic418967fa.accept_13_7_3_1_1_814 59 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 224 287 (accept_3_2 58 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 224 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 224 287 7 8 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 224 287 (accept_3_2 55 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 224 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 224 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 224 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 224
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 224 287 (accept_3_2 52 224
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 224 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 51 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 224 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 224 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 224 287 7 7 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 224 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888
  48 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 224 287
  (Polychromatic418967fa.accept_19_9_15_2_1_9758 47 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 224 287 (accept_3_2 46 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 224 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 224 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 224 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 224 287 (accept_3_2 43 224 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 224 287 7 6 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 224 287 (Polychromatic418967fa.accept_10_1_4_7_1_374
  41 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 224 287 (accept_3_2 40
  224 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 224 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 224 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 224 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 224 287 (accept_3_2 37 224 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 224 287 (Polychromatic418967fa.accept_19_17_15_2_1_6887 36 224 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 224 287 7 5 32 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 224 287 (accept_3_2 34 224 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 224 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 224 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 224 287 (accept_3_2 31 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 224 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 224 287 (Polychromatic418967fa.accept_17_12_3_15_1_5476 29 224 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 224 287 7 4 32 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 224 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 224 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 224 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 224 287 (accept_3_2 25 224 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 224 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 224 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 224 287
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 224 287 (accept_3_2 22 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  224 287 7 3 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 224 287 (Polychromatic418967fa.accept_13_7_3_1_1_814 20 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 224 287 (accept_3_2 19 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 224 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 224 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 224 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 224
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 224 287 (accept_3_2 16 224
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 224 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 224 287 7 2 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 224 287 (accept_3_2 13 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 224 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 224 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 224 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 224 287 (accept_3_2 10 224 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 224 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 224 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 224 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 224 287 7 1 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 224 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 224 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 224 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 224 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 287 (accept_3_2 4 224 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 224 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3
  224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 224 287 (accept_3_2 1 224 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 223 287 (Eq.refl Bool.true)
  (allA_of_3_0 65 223 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 222 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 222 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 222 287 (accept_3_2 64 222 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 222 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 222 287
  (Polychromatic418967fa.accept_22_18_2_1_1_6765 62 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 222 287 (accept_3_2 61 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 222 287 (Polychromatic418967fa.accept_17_9_1_15_1_3156 60 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 222 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 222 287 (accept_3_2 58 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 222 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 222 287 (accept_3_2 55 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 222 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 222 287 (accept_3_2 52 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 222 287 (Polychromatic418967fa.accept_14_9_12_7_1_597 51 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 222 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 222 287 (accept_3_2 49 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 222 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 222 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 222 287 (accept_3_2 46 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 222 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 222 287 (accept_3_2 43 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 222 287 (Polychromatic418967fa.accept_16_10_14_15_1_2933 42 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 222 287 (accept_3_2 40 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 222 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 222 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 222 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 222 287 (accept_3_2 37 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 222 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 222 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 222 287 (accept_3_2 34 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 222 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 222 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 222 287 (accept_3_2 31 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 222 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 222 287 (accept_3_2 28 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 222 287 (Polychromatic418967fa.accept_19_8_13_2_1_6921 27 222 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 222 287
  (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 222 287 (accept_3_2 25 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 222 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 222 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 222 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 222 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 222 287 (accept_3_2 22 222 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 222 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 222 287 (accept_3_2 19 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 222 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 287 (accept_3_2 16 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 222 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 222 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 222 287 (accept_3_2 13 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 222 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 222 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 222 287 (accept_3_2 10 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 287
  (Polychromatic418967fa.accept_19_8_13_2_1_6921 8 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 222 287 (accept_3_2 7 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  222 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 222 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 287 (accept_3_2 4 222 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 222 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 222 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 222 287 (accept_3_2 1 222 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 221 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 221 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 221 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 221 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 221 287 (accept_3_2 64 221 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 221 287
  (Polychromatic418967fa.accept_19_6_12_2_1_8379 63 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 221 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 221 287 (accept_3_2 61 221 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 221 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 221 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 221 287
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 59 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 221 287 (accept_3_2 58 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 221 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 221 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 221 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 221 287 (accept_3_2 55 221 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 221 287
  (Polychromatic418967fa.accept_23_7_14_11_1_17658 53 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 221 287 (accept_3_2 52 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 221 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 221 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 221 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 221 287 (accept_3_2 49 221 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 221 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48
  221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 221 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 221 287 (accept_3_2 46 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 221 287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 221 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 44 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 221 287 (accept_3_2 43 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 221 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 221 287
  (Polychromatic418967fa.accept_19_3_12_2_1_9788 41 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 221 287 (accept_3_2 40 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 221 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 221 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 221 287 (accept_3_2 37 221 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 221 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 221 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 221 287 (accept_3_2 34 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 221 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 221 287 (Polychromatic418967fa.accept_14_4_11_7_1_1234 32 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 221 287 (accept_3_2 31 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 221 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 221 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 221 287 (accept_3_2 28 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 221 287 (Polychromatic418967fa.accept_21_6_11_14_1_11812 27 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 221 287 (accept_3_2 25 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 221 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 221 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 221 287
  (Polychromatic418967fa.accept_19_4_12_2_1_11158 23 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 221 287 (accept_3_2 22 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 221 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 221 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 221 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 287 (accept_3_2 19 221 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 287
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 221 287 (accept_3_2 16 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 221 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 221 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 287 (accept_3_2 13 221 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 221 287 (accept_3_2 10 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  221 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 221 287 (Polychromatic418967fa.accept_18_8_5_17_1_1388 8 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 287 (accept_3_2 7 221 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 221 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 287 (accept_3_2 4 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 221 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 221 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 287 (accept_3_2 1 221 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 221 287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 220 287 (Eq.refl Bool.true) (allA_of_3_0 68 220 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 219 287
  (Eq.refl Bool.true) (allA_succ_of_accept 68 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 219 287 (accept_3_2 67 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 219 287 (Polychromatic418967fa.accept_20_6_19_7_1_3375 66 219
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 219 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 219 287 (accept_3_2 64 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 219 287 (Polychromatic418967fa.accept_19_6_10_2_1_6874 63 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 219 287 (accept_3_2 61 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 219 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 219 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 219 287 (accept_3_2 58 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 219 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 219 287 (accept_3_2 55 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 219 287 (Polychromatic418967fa.accept_14_12_9_7_1_2762 54 219 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 219 287
  (Polychromatic418967fa.accept_11_9_10_1_1_581 53 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 219 287 (accept_3_2 52 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 219 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 219 287 (accept_3_2 49 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 219 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 219 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 219 287 (accept_3_2 46 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 219 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 287 (accept_3_2 43 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 219 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 219 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 219 287 (accept_3_2 40 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 219 287 (Polychromatic418967fa.accept_16_7_11_15_1_2929 39 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 287 (accept_3_2 37 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 219 287
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 219 287 (accept_3_2 34 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 219 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 287 (accept_3_2 31 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 287 (Polychromatic418967fa.accept_14_2_9_7_1_5633 30 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 219 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 219 287 (accept_3_2 28 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 219 287 (Polychromatic418967fa.accept_19_8_10_2_1_5414 27 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 287 (accept_3_2 25 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 219 287 (accept_3_2 22 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 219 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 287 (accept_3_2 19 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 287
  (Polychromatic418967fa.accept_16_1_11_15_1_498 17 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 287 (accept_3_2 16 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 219 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 287 (accept_3_2 13 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 287 (accept_3_2 10 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  219 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 287 (accept_3_2 7 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 219 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 287 (accept_3_2 4 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 219 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 287 (accept_3_2 1 219 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 219 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 218 287 (Eq.refl Bool.true) (allA_succ_of_accept 69 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  69 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 218 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 218 287 (accept_3_2 67 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 218 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 218 287 (accept_3_2 64 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 218 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 218 287
  (Polychromatic418967fa.accept_14_6_8_7_1_589 62 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 218 287 (accept_3_2 61 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 218 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 218 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 218 287 (accept_3_2 58 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 218 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 218 287 (accept_3_2 55 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 218 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 218 287 (accept_3_2 52 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 218 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 218 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 218 287 (accept_3_2 49 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 218 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 218 287 (Polychromatic418967fa.accept_18_11_2_17_1_3490 47 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 218 287 (accept_3_2 46 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 218 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 218 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 218 287 (accept_3_2 43 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 218 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 218 287 (accept_3_2 40 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 218 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 218 287
  (Polychromatic418967fa.accept_21_17_8_14_1_5638 38 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 218 287 (accept_3_2 37 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 218 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 218 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 218 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 218
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 218 287 (accept_3_2 34 218
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  33 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 218 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 218 287 (accept_3_2 31 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 218 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 218 287 (accept_3_2 28 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 218 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 218 287
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 218 287 (accept_3_2 25 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 218 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 218 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 218 287 (accept_3_2 22 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 218 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 218 287 (accept_3_2 19 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 218 287 (Polychromatic418967fa.accept_19_18_9_2_1_9764 18 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 218 287 (accept_3_2 16 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 218 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 218 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 218 287 (accept_3_2 13 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 218 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 218 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 218 287 (accept_3_2 10 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 218 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 218 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 218 287 (accept_3_2 7 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  218 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 218 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 218 287 (accept_3_2 4 218 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 218 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 218 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 218 287
  (Polychromatic418967fa.accept_20_2_18_7_1_3394 2 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 218 287 (accept_3_2 1 218 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 217 287 (Eq.refl Bool.true)
  (allA_of_3_0 71 217 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 216 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 216 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 71 216 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 216 287 (accept_3_2 70 216 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 216 287 (Polychromatic418967fa.accept_14_13_6_7_1_2013 69 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 216 287
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 68 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 216 287 (accept_3_2 67 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 216 287 (Polychromatic418967fa.accept_19_9_7_2_1_6868 66 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 216 287 (Polychromatic418967fa.accept_16_1_8_15_1_1945 65 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 216 287 (accept_3_2 64 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 216 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 216 287
  (Polychromatic418967fa.accept_19_5_7_2_1_1728 62 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 216 287 (accept_3_2 61 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 216 287 (Polychromatic418967fa.accept_16_12_8_15_1_5119 60 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 216 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 59 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 216 287 (accept_3_2 58 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 216 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 57 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 216 287
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 56 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 216 287 (accept_3_2 55 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 216 287 (Polychromatic418967fa.accept_17_3_12_15_1_1203 54 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 216 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 53 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 216 287 (accept_3_2 52 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 216 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 51 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 216 287
  (Polychromatic418967fa.accept_11_6_7_1_1_564 50 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 216 287 (accept_3_2 49 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 216 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 48 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 216 287 (Polychromatic418967fa.accept_19_9_7_2_1_6868 47 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 216 287 (accept_3_2 46 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 216 287 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 216 287
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 216 287 (accept_3_2 43 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 216 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 42 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 216 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 41 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 216 287 (accept_3_2 40 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 216 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 216 287
  (Polychromatic418967fa.accept_13_12_8_1_1_825 38 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 216 287 (accept_3_2 37 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 216 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 216 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 35 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 216 287 (accept_3_2 34 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 216 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 216 287
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 32 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 216 287 (accept_3_2 31 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 216 287 (Polychromatic418967fa.accept_21_9_6_14_1_7228 30 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 216 287 (Polychromatic418967fa.accept_14_1_6_7_1_1936 29 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 216 287 (accept_3_2 28 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 216 287 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 216 287
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 216 287 (accept_3_2 25 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 216 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 216 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 287 (accept_3_2 22 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 216 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 216 287
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 20 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 216 287 (accept_3_2 19 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 216 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 216 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 216 287 (accept_3_2 16 216 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 216 287 (Polychromatic418967fa.accept_14_1_6_7_1_1936 15 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 287
  (Polychromatic418967fa.accept_17_14_12_15_1_5558 14 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 216 287 (accept_3_2 13 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 216 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 216 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 216 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 216 287 (accept_3_2 10 216
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 216 287
  (Polychromatic418967fa.accept_13_9_8_1_1_824 9 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 216 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 216 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 287 (accept_3_2 7 216 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 216 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 216 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161
  5 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 287 (accept_3_2 4
  216 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 216 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 216 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 216 287 (Polychromatic418967fa.accept_21_2_6_14_1_1569 2 216 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 287 (accept_3_2 1 216 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 216 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73
  215 287 (Eq.refl Bool.true) (allA_succ_of_accept 72 215 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 215 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 215 287
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 215 287 (accept_3_2 70 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 215 287 (Polychromatic418967fa.accept_19_12_6_2_1_5424 69 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 215 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 68 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 215 287 (accept_3_2 67 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 215 287 (Polychromatic418967fa.accept_23_20_8_11_1_11355 66
  215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 215 287
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 65 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 215 287 (accept_3_2 64 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 215 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 215 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 62 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 215 287 (accept_3_2 61 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 215 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 215
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 215 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 59 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 215 287 (accept_3_2 58 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 215 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 57 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 215 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 215 287 (accept_3_2 55 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 215 287 (Polychromatic418967fa.accept_14_12_5_7_1_2010 54 215
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 215 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 215 287 (accept_3_2 52 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 215 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 215 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 50 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 215 287 (accept_3_2 49 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 215 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 215
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 215 287
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 47 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 215 287 (accept_3_2 46 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 215 287 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 215 287 (Polychromatic418967fa.accept_14_2_5_7_1_3767 44 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 215 287 (accept_3_2 43 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 215 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 215
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 215 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 41 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 215 287 (accept_3_2 40 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 215 287 (Polychromatic418967fa.accept_17_5_11_15_1_5445 39 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 215 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 38 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 287 (accept_3_2 37 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 287 (Polychromatic418967fa.accept_21_15_5_14_1_11856 36
  215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 215 287
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 35 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 215 287 (accept_3_2 34 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 215 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 215 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 287 (accept_3_2 31 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 287 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 215
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 215 287
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 215 287 (accept_3_2 28 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 215 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 215 287 (Polychromatic418967fa.accept_14_12_5_7_1_2010 26 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 287 (accept_3_2 25 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 215 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 215
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 215 287 (accept_3_2 22 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 215 287 (Polychromatic418967fa.accept_19_1_6_2_1_8341 20 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 287 (accept_3_2 19 215 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 215
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 287
  (Polychromatic418967fa.accept_21_17_5_14_1_4144 17 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 215 287 (accept_3_2 16 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 215 287 (Polychromatic418967fa.accept_19_15_6_2_1_6865 15 215 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 287 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 215
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 287 (accept_3_2 13 215
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 287
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 215 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 215 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 287 (accept_3_2 10 215 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 215 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 215 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 8
  215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 287 (accept_3_2 7 215
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 287
  (Polychromatic418967fa.accept_13_6_7_1_1_335 6 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 215 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 215 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 287 (accept_3_2 4 215 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 215 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 215 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124
  2 215 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 287 (accept_3_2 1
  215 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 214 287 (Eq.refl
  Bool.true) (allA_of_3_0 74 214 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 213 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 74 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 213 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 213 287 (accept_3_2 73 213 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 213 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 213 287
  (Polychromatic418967fa.accept_13_6_5_1_1_834 71 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 213 287 (accept_3_2 70 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 213 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 69 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 213 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 213 287 (accept_3_2 67 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 213 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 213 287 (accept_3_2 64 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 213 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 213 287 (accept_3_2 61 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 213 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 60 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 213 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 213 287 (accept_3_2 58 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 213 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 213 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 287 (accept_3_2 55 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 213 287
  (Polychromatic418967fa.accept_14_11_3_7_1_604 53 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 213 287 (accept_3_2 52 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 213 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 287 (accept_3_2 49 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 213 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 213 287 (accept_3_2 46 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 213 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 213 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 287 (accept_3_2 43 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 213 287 (accept_3_2 40 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 213 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 287 (accept_3_2 37 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 213 287 (accept_3_2 34 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 213 287 (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 213 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 287 (accept_3_2 31 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 287 (accept_3_2 28 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 213 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 287 (accept_3_2 25 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 287 (accept_3_2 22 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 213 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 213 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 287 (accept_3_2 19 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 287
  (Polychromatic418967fa.accept_13_4_5_1_1_833 17 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 287 (accept_3_2 16 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 213 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 287 (accept_3_2 13 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 287 (accept_3_2 10 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 287 (accept_3_2 7 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 213 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 287 (accept_3_2 4 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 213 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 287 (accept_3_2 1 213 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 76 212 287 (Eq.refl Bool.true) (allA_succ_of_accept 75 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32
  75 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 212 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 212 287 (accept_3_2 73 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 212 287 (Polychromatic418967fa.accept_16_8_4_15_1_2941 72 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 212 287 (Polychromatic418967fa.accept_21_8_2_14_1_10496 71 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 212 287 (accept_3_2 70 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 212 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 212 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 68 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 212 287 (accept_3_2 67 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 212 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 212 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 212 287 (accept_3_2 64 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 212 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 212 287 (accept_3_2 61 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 212 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 212 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 212 287 (accept_3_2 58 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 212 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 212 287 (accept_3_2 55 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 212 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 212 287 (Polychromatic418967fa.accept_16_5_4_15_1_1102 53 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 212 287 (accept_3_2 52 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 212 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 212 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 212 287 (accept_3_2 49 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 212 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 212 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 212 287 (accept_3_2 46 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 212 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 212 287 (accept_3_2 43 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 212 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 212 287 (Polychromatic418967fa.accept_21_20_2_14_1_5687 41 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 212 287 (accept_3_2 40 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 212 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 212 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 212 287 (accept_3_2 37 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 212 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 212 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 212 287 (accept_3_2 34 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 212 287
  (Polychromatic418967fa.accept_21_11_2_14_1_7225 32 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 212 287 (accept_3_2 31 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 212 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 212 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 212 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 212 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 212 287 (accept_3_2 28 212 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 212 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 212 287 (accept_3_2 25 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 212 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 212 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 212 287 (accept_3_2 22 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 212 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 212 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 212 287 (accept_3_2 19 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 212 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 212 287 (Polychromatic418967fa.accept_19_17_3_2_1_1725 17 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 212 287 (accept_3_2 16 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 212 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 212 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 212 287 (accept_3_2 13 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 212 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 212 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 212 287 (accept_3_2 10 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 212 287
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 212 287 (accept_3_2 7 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  212 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 212 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 212 287 (accept_3_2 4 212 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 212 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 212 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 212 287 (accept_3_2 1 212 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 211 287 (Eq.refl
  Bool.true) (allA_of_3_0 77 211 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 210 287 (Eq.refl Bool.true)
  (allA_succ_of_gcd 77 210 287 7 11 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 210 287 (accept_3_2 76 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 210 287 (Polychromatic418967fa.accept_19_18_1_2_1_5430 75 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 210 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 210 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 210 287 (accept_3_2 73 210 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 210 287
  (Polychromatic418967fa.accept_19_15_1_2_1_6894 72 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 210 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 71 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 210 287 7 10 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 210 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69
  210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 210 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 210 287 (accept_3_2 67 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 210 287 (Polychromatic418967fa.accept_19_9_1_2_1_6839 66 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 210 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 210 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 210 287 (accept_3_2 64 210 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 63 210 287 7 9 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 210 287 (Polychromatic418967fa.accept_26_10_2_1_1_17657 62 210
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 210 287 (accept_3_2 61 210
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 210 287
  (Polychromatic418967fa.accept_9_6_3_8_1_595 60 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 210 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 210 287 (accept_3_2 58 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 210 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 210 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 210 287 7 8 30 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 210 287 (accept_3_2 55 210 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 210 287 (Polychromatic418967fa.accept_23_8_3_11_1_14511 54 210
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 210 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 210 287 (accept_3_2 52 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 210 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 210 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 210 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 210 287 7 7 30 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 210 287
  (Polychromatic418967fa.accept_13_9_2_1_1_813 48 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 210 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 210 287 (accept_3_2 46 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 210 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 210 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 210 287
  (Polychromatic418967fa.accept_16_12_2_15_1_490 44 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 210 287 (accept_3_2 43 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  210 287 7 6 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 210 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 210 287 (accept_3_2 40 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 210 287 (Polychromatic418967fa.accept_20_19_10_7_1_7877 39 210 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 210 287 (Polychromatic418967fa.accept_9_2_3_8_1_318
  38 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 210 287 (accept_3_2 37
  210 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 210 287
  (Polychromatic418967fa.accept_24_12_18_23_1_16060 36 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 210 287 7 5 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 210 287 (accept_3_2 34 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 210 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 210 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 210 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 210 287 (accept_3_2 31 210 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 210 287
  (Polychromatic418967fa.accept_22_8_12_1_1_13175 30 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 210 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 210 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 287 7 4 30 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 210 287
  (Polychromatic418967fa.accept_18_9_12_17_1_6060 27 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 210 287 (Polychromatic418967fa.accept_17_9_6_15_1_5454 26 210 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 210 287 (accept_3_2 25 210 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 210 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 210 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 210 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 210 287 (accept_3_2 22 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  210 287 7 3 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 210 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 210 287 (accept_3_2 19 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 210 287 (Polychromatic418967fa.accept_19_18_1_2_1_5430 18 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 210 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 210 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 287 (accept_3_2 16 210 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 210 287 (Polychromatic418967fa.accept_9_6_3_8_1_595
  15 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 210 287 7 2 30 41
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 287
  (accept_3_2 13 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 210 287
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 210 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 287 (accept_3_2 10 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 210 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 210 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 287 (Polychromatic418967fa.accept_17_8_6_15_1_523
  8 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 210 287 7 1 30 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 210 287
  (Polychromatic418967fa.accept_9_6_3_8_1_595 6 210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 210 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 287 (accept_3_2 4 210 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 210 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 210 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  210 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 287 (accept_3_2 1 210
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 209 287 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 209 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 209 287 (Polychromatic418967fa.accept_9_5_2_8_1_109
  77 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 209 287 (accept_3_2 76
  209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 209 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 209 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 209 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 209 287 (accept_3_2 73 209 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 209 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 209 287
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 71 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 209 287 (accept_3_2 70 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 209 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 209 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 209 287 (accept_3_2 67 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 209 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 209 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 209 287 (accept_3_2 64 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 209 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 209 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 209 287 (accept_3_2 61 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 209 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 209 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 209 287 (accept_3_2 58 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 209 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 209 287 (Polychromatic418967fa.accept_16_8_1_15_1_1982 56 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 209 287 (accept_3_2 55 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 209 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 209 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 209 287
  (Polychromatic418967fa.accept_16_5_1_15_1_3922 53 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 209 287 (accept_3_2 52 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 209 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 209 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 209 287 (accept_3_2 49 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 209 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 209 287
  (Polychromatic418967fa.accept_17_13_5_15_1_8103 47 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 209 287 (accept_3_2 46 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 209 287 (Polychromatic418967fa.accept_17_11_5_15_1_8144 45 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 209 287
  (Polychromatic418967fa.accept_17_10_5_15_1_4332 44 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 209 287 (accept_3_2 43 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 209 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 209 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 209 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 209 287 (accept_3_2 40 209 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 209 287 (Polychromatic418967fa.accept_9_3_2_8_1_108
  39 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 209 287 (accept_3_2 37 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 209 287 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 209 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 209 287 (accept_3_2 34 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 209 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 209 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 209 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 209 287 (accept_3_2 31 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 209 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 209 287 (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 209 287 (accept_3_2 28 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 209 287 (Polychromatic418967fa.accept_15_12_14_2_1_3794 27 209
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 209 287 (accept_3_2 25 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 209 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 209 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 287 (accept_3_2 22 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 209 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 287
  (Polychromatic418967fa.accept_14_6_13_7_1_2015 20 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 209 287 (accept_3_2 19 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 209 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 209 287 (Polychromatic418967fa.accept_20_17_9_7_1_13576 17 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 287 (accept_3_2 16 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 209 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 287 (accept_3_2 13 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 287 (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 287 (accept_3_2 10 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 287 (Polychromatic418967fa.accept_21_9_20_14_1_4139 9 209
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 287
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 287 (accept_3_2 7 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 287 (accept_3_2 4 209 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 209 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 287 (accept_3_2 1 209 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 208 287 (Eq.refl
  Bool.true) (allA_of_3_0 80 208 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 207 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 80 207 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 207 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 207 287 (accept_3_2 79 207 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 207 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 78 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 207 287
  (Polychromatic418967fa.accept_24_5_15_23_1_5647 77 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 207 287 (accept_3_2 76 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 207 287 (Polychromatic418967fa.accept_21_12_18_14_1_8854 75 207 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 207 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 74
  207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 207 287 (accept_3_2 73
  207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 207 287
  (Polychromatic418967fa.accept_19_15_17_2_1_4097 72 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 207 287 (Polychromatic418967fa.accept_19_14_17_2_1_1720 71 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 207 287 (accept_3_2 70 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 207 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 207
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 207 287 (accept_3_2 67 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 207 287 (Polychromatic418967fa.accept_14_10_11_7_1_1955 66 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 207 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 207 287 (accept_3_2 64 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 207 287 (Polychromatic418967fa.accept_13_11_12_1_1_2154 63 207
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 207 287 (accept_3_2 61 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 207 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 60 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 207 287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 59 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 207 287 (accept_3_2 58 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 207 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 207
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 207 287 (accept_3_2 55 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 207 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 207 287 (Polychromatic418967fa.accept_19_15_17_2_1_4097 53 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 207 287 (accept_3_2 52 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 207 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 207
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 207 287 (accept_3_2 49 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 207 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 207 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 207 287 (accept_3_2 46 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 207 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 207
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 207 287 (accept_3_2 43 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 207 287 (Polychromatic418967fa.accept_19_4_17_2_1_5409 42 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 207 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 41 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 287 (accept_3_2 40 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 207 287 (Polychromatic418967fa.accept_26_13_25_1_1_17656 39
  207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 207 287 (accept_3_2 37 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 207 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 207 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 287 (accept_3_2 34 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 207
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 207 287 (accept_3_2 31 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 207 287 (Polychromatic418967fa.accept_18_12_9_17_1_7428 30 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 207 287 (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 287 (accept_3_2 28 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 287 (Polychromatic418967fa.accept_21_6_18_14_1_14768 27
  207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 287 (accept_3_2 25 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 207 287 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 207 287 (Polychromatic418967fa.accept_19_4_17_2_1_5409 23 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 287 (accept_3_2 22 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 207
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 287 (accept_3_2 19 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 207 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 207 287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 287 (accept_3_2 16 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 207
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 287 (accept_3_2 13 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 207 287 (Polychromatic418967fa.accept_17_12_3_15_1_5476 12 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 207 287 (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 287 (accept_3_2 10 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 207
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 287 (accept_3_2 7 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  207 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 207 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 287 (accept_3_2 4 207 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 207
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 287 (accept_3_2 1 207 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 206 287 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 206 287 (Polychromatic418967fa.accept_12_8_2_11_1_246
  80 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 206 287 (accept_3_2 79
  206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 206 287
  (Polychromatic418967fa.accept_17_10_2_15_1_3179 78 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 206 287 (accept_3_2 76 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 206 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 206 287
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 74 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 206 287 (accept_3_2 73 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 206 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 206 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 71 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 206 287 (accept_3_2 70 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 206 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 206 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 206 287 (accept_3_2 67 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 206 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 66 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 206 287 (accept_3_2 64 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 206 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 206 287
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 62 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 206 287 (accept_3_2 61 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 206 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 206 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 206 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 206
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 206 287 (accept_3_2 58 206
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  57 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 206 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 206 287 (accept_3_2 55 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 206 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 206 287 (accept_3_2 52 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 206 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 206 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 50 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 206 287 (accept_3_2 49 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 206 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 206 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 47 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 206 287 (accept_3_2 46 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 206 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 206 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 206 287 (accept_3_2 43 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 206 287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 206 287 (accept_3_2 40 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 206 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 206 287
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 38 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 206 287 (accept_3_2 37 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 206 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 206 287
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 206 287 (accept_3_2 34 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 206 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 206 287 (accept_3_2 31 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 206 287 (Polychromatic418967fa.accept_17_13_2_15_1_2151 30 206
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 206 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 206 287 (accept_3_2 28 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 206 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 206 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 206 287 (accept_3_2 25 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 206 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 24 206
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 206 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 206 287 (accept_3_2 22 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 206 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 206 287 (accept_3_2 19 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 206 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 206
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 206 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 206 287 (accept_3_2 16 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 206 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 206 287 (Polychromatic418967fa.accept_19_14_16_2_1_6952 14 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 206 287 (accept_3_2 13 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 206 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 206
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 206 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 206 287 (accept_3_2 10 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  206 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 206 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 206 287 (accept_3_2 7 206 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 206 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 6 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 206 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 206 287 (accept_3_2 4 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  206 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 206 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 206 287 (Polychromatic418967fa.accept_18_2_8_17_1_4754 2 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 206 287 (accept_3_2 1 206 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 206
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 205 287 (Eq.refl
  Bool.true) (allA_of_3_0 83 205 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 204 287 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 204 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 204 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 204 287 (accept_3_2 82 204 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 204 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 81 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 204 287
  (Polychromatic418967fa.accept_13_2_9_1_1_67 80 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 204 287 (accept_3_2 79 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 204 287 (Polychromatic418967fa.accept_23_9_20_11_1_4501 78 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 204 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 204 287 (accept_3_2 76 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 204 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 204 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 204 287 (accept_3_2 73 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 204 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 204 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 71 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 204 287 (accept_3_2 70 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 204 287 (Polychromatic418967fa.accept_14_13_8_7_1_1224 69 204
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 204 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 204 287 (accept_3_2 67 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 204 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 204 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 204 287 (accept_3_2 64 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 204 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 204 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 62 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 204 287 (accept_3_2 61 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 204 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 204 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 204 287 (accept_3_2 58 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 204 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 204 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 204 287 (accept_3_2 55 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 204 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 54 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 204 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 204 287 (accept_3_2 52 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 204 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 204 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 204 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 204 287 (accept_3_2 49 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 204 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 204 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 204 287 (accept_3_2 46 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 204 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 204 287
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 44 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 204 287 (accept_3_2 43 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 204 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 204 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 204 287 (accept_3_2 40 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 204 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 204 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 204 287 (accept_3_2 37 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 204 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 204 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 204 287 (accept_3_2 34 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 204 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 204 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 204 287 (accept_3_2 31 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 204 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 204 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 204 287 (accept_3_2 28 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 204 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 287
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 204 287 (accept_3_2 25 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 204 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 204 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 204 287 (accept_3_2 22 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 204 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 204 287 (accept_3_2 19 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 204 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 204 287 (Polychromatic418967fa.accept_19_17_14_2_1_4116 17 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 204 287 (accept_3_2 16 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 204 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 15 204 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 204 287 (accept_3_2 13 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 204 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 204 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 287 (accept_3_2 10 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 204 287 (Polychromatic418967fa.accept_21_9_15_14_1_2790 9 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 287
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 204 287 (accept_3_2 7 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  204 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 204 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 204 287 (accept_3_2 4 204 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 204 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 204 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 204 287 (accept_3_2 1 204 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 203 287
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 203 287 7 12 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 203 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 203 287 (accept_3_2 82 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 203 287 (Polychromatic418967fa.accept_15_6_8_2_1_104
  81 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 203 287
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 80 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 203 287 (accept_3_2 79 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 203 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 77 203 287 7 11 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 203 287 (accept_3_2 76 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 203 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 203 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 203 287 (accept_3_2 73 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 203 287 (Polychromatic418967fa.accept_11_6_5_1_1_586
  72 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 203 287
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 71 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 203 287 7 10 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 203 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 203 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 203 287 (Polychromatic418967fa.accept_8_4_3_7_1_491
  68 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 203 287 (accept_3_2 67
  203 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 203 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 66 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 203 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 203 287 (accept_3_2 64 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 203 287 7 9 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 203 287 (Polychromatic418967fa.accept_17_11_16_15_1_5467 62 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 203 287 (accept_3_2 61 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 203 287 (Polychromatic418967fa.accept_8_4_3_7_1_491
  60 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 203 287
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 59 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 203 287 (accept_3_2 58 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 203 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 203 287 7 8 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 203 287 (accept_3_2 55 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 203 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 203 287 (Polychromatic418967fa.accept_19_15_13_2_1_6851 53 203
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 203 287 (accept_3_2 52 203
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 203 287
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 203 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 203 287 7 7 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 203 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48
  203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 203 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 203 287 (accept_3_2 46 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 203 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 203 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 203 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 203 287 (accept_3_2 43 203 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 203 287 7 6 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 203 287 (Polychromatic418967fa.accept_24_17_11_23_1_17632 41
  203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 203 287 (accept_3_2 40
  203 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 203 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 203 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 287 (accept_3_2 37 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 203 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 203 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 203 287 7 5 29 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 203 287 (accept_3_2 34 203 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 203 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 203 287
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 32 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 203 287 (accept_3_2 31 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 203 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 203 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 203 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 203 287 7 4 29 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 203 287
  (Polychromatic418967fa.accept_19_8_13_2_1_6921 27 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 203 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 287 (accept_3_2 25 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 203 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 203 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 287
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 203 287 (accept_3_2 22 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 203 287 7 3 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 203 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 287 (accept_3_2 19 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 203 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 203 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 287 (accept_3_2 16 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 203 287 7 2 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 203 287 (accept_3_2 13 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 203 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 287 (accept_3_2 10 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 9
  203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 287
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 8 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 203 287 7 1 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 203 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 203 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 287 (accept_3_2 4 203 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3
  203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 287 (accept_3_2 1 203 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 202 287
  (Eq.refl Bool.true) (allA_of_3_0 86 202 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 201 287 (Eq.refl
  Bool.true) (allA_succ_of_accept 86 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 201 287 (accept_3_2 85 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 201 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 84 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 201 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 201 287 (accept_3_2 82 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 201 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 81 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 201 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 201 287 (accept_3_2 79 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 201 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 201 287 (accept_3_2 76 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 201 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 201 287 (accept_3_2 73 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 201 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 72 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 201 287
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 71 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 201 287 (accept_3_2 70 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 201 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 201 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 201 287 (accept_3_2 67 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 201 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 201 287 (accept_3_2 64 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 201 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 201 287 (accept_3_2 61 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 201 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 201 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 201 287 (accept_3_2 58 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 201 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 201 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 287 (accept_3_2 55 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 201 287
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 201 287 (accept_3_2 52 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 201 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 287 (accept_3_2 49 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 201 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 48 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 201 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 201 287 (accept_3_2 46 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 201 287 (Polychromatic418967fa.accept_21_3_12_14_1_8848 45 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 201 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 287 (accept_3_2 43 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 201 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 201 287 (accept_3_2 40 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 201 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 287 (accept_3_2 37 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 201 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 201 287 (accept_3_2 34 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 201 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 201 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 287 (accept_3_2 31 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 201 287 (accept_3_2 28 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 201 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 287 (accept_3_2 25 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 201 287 (accept_3_2 22 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 201 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 201 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 287 (accept_3_2 19 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 201 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 287
  (Polychromatic418967fa.accept_25_17_1_12_1_17655 17 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 201 287 (accept_3_2 16 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 201 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 201 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 201 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 287 (accept_3_2 13 201 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 287
  (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 201 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 201 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 287 (accept_3_2 10 201 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 201 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8
  201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 287 (accept_3_2 7 201
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27
  6 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 287 (accept_3_2 4 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 201 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 287 (accept_3_2 1 201 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 200 287
  (Eq.refl Bool.true) (allA_succ_of_accept 87 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 200 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 200 287 (accept_3_2 85 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 200 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 200 287 (Polychromatic418967fa.accept_18_11_2_17_1_3490 83 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 200 287 (accept_3_2 82 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 200 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 200 287
  (Polychromatic418967fa.accept_11_3_2_1_1_994 80 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 200 287 (accept_3_2 79 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 200 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 200 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 200 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 200 287 (accept_3_2 76 200 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 200 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 200 287 (accept_3_2 73 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 200 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 72 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 200 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 71 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 200 287 (accept_3_2 70 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 200 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 200 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 200 287 (accept_3_2 67 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 200 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 200 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 200 287 (accept_3_2 64 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 200 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 200 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 200 287 (accept_3_2 61 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 200 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 200 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 200 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 200 287 (accept_3_2 58 200 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 200 287
  (Polychromatic418967fa.accept_13_4_5_1_1_833 56 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 200 287 (accept_3_2 55 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 200 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 200 287 (Polychromatic418967fa.accept_14_11_4_7_1_609 53 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 200 287 (accept_3_2 52 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 200 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 200 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 200 287 (accept_3_2 49 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 200 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 200 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 200 287 (accept_3_2 46 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 200 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 200 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 44 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 200 287 (accept_3_2 43 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 200 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 200 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 200 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 200 287 (accept_3_2 40 200 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 200 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 200 287 (accept_3_2 37 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 200 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 200 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 200 287 (accept_3_2 34 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 200 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 200 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 200 287 (accept_3_2 31 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 200 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 200 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 200 287 (accept_3_2 28 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 200 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 200 287 (accept_3_2 25 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 200 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 200 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 200 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 287 (accept_3_2 22 200 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 200 287
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 20 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 200 287 (accept_3_2 19 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 200 287 (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 200 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 200 287 (accept_3_2 16 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 200 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 200 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 200 287 (accept_3_2 13 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 200 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 200 287 (Polychromatic418967fa.accept_14_11_4_7_1_609 11 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 200 287 (accept_3_2 10 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 287
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 200 287 (accept_3_2 7 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  200 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 200 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 200 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 287 (accept_3_2 4 200 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 287 (accept_3_2 1 200 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 199 287
  (Eq.refl Bool.true) (allA_of_3_0 89 199 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 198 287 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 198 287 (accept_3_2 88 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 198 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 87 198 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 198 287
  (Polychromatic418967fa.accept_19_10_8_2_1_831 86 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 198 287 (accept_3_2 85 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 198 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 84 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 198 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 83 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 198 287 (accept_3_2 82 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 198 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 198 287
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 80 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 198 287 (accept_3_2 79 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 198 287 (Polychromatic418967fa.accept_21_15_9_14_1_10462 78 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 77 198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 198 287 (accept_3_2 76 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 198 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 75 198
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 198 287
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 74 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 198 287 (accept_3_2 73 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 198 287 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 198 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 71 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 198 287 (accept_3_2 70 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 198 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 198 287
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 68 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 198 287 (accept_3_2 67 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 198 287 (Polychromatic418967fa.accept_21_3_9_14_1_5701 66 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 198 287 (accept_3_2 64 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 198 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 198 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 198 287
  (Polychromatic418967fa.accept_19_5_8_2_1_1707 62 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 198 287 (accept_3_2 61 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 198 287 (Polychromatic418967fa.accept_21_18_9_14_1_8832 60 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 198 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 59 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 198 287 (accept_3_2 58 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 198 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 198 287
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 56 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 198 287 (accept_3_2 55 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 198 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 198 287 (accept_3_2 52 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 198 287 (Polychromatic418967fa.accept_14_9_2_7_1_1242 51 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 198 287
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 50 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 198 287 (accept_3_2 49 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 198 287 (Polychromatic418967fa.accept_19_10_8_2_1_831 48 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 198 287 (Polychromatic418967fa.accept_14_5_2_7_1_2804 47 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 198 287 (accept_3_2 46 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 198 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 198 287
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 198 287 (accept_3_2 43 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 198 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 198 287 (accept_3_2 40 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 198 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 198 287
  (Polychromatic418967fa.accept_17_4_11_15_1_3170 38 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 198 287 (accept_3_2 37 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 198 287 (Polychromatic418967fa.accept_21_15_9_14_1_10462 36 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 198 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  35 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 198 287 (accept_3_2 34
  198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 198 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 198 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 32 198 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 287 (accept_3_2 31 198 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 198 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 198 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 198 287 (accept_3_2 28 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 198 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 198 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 287 (accept_3_2 25 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 198
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 198 287
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 23 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 198 287 (accept_3_2 22 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 198 287 (Polychromatic418967fa.accept_13_7_3_1_1_814 20 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 287 (accept_3_2 19 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 198
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 198 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 198 287 (accept_3_2 16 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 198 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 198 287 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 287 (accept_3_2 13 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 198
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 198 287
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 198 287 (accept_3_2 10 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  198 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 198 287 (Polychromatic418967fa.accept_27_8_9_17_1_17654 8 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 287 (accept_3_2 7 198 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 198 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 198 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 198 287 (accept_3_2 4 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  198 287 (Polychromatic418967fa.accept_21_3_9_14_1_5701 3 198 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 198 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 287 (accept_3_2 1 198 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 198
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 197 287
  (Eq.refl Bool.true) (allA_succ_of_accept 90 197 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 197 287
  (Polychromatic418967fa.accept_17_4_10_15_1_5444 89 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 197 287 (accept_3_2 88 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 197 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 87 197 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 197 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 197 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 197 287 (accept_3_2 85 197 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 197 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137
  84 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 197 287
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 83 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 197 287 (accept_3_2 82 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 197 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 81 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 197 287 (Polychromatic418967fa.accept_19_4_7_2_1_6944 80 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 197 287 (accept_3_2 79 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 197 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 197 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 197 287
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 77 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 197 287 (accept_3_2 76 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 197 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 75 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 197 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 197 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 197 287 (accept_3_2 73 197 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 197 287 (Polychromatic418967fa.accept_17_4_10_15_1_5444 72 197 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 197 287
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 71 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 197 287 (accept_3_2 70 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 197 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 69 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 197 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 68 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 197 287 (accept_3_2 67 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 197 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 197 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 197 287
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 65 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 197 287 (accept_3_2 64 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 197 287 (Polychromatic418967fa.accept_23_17_13_11_1_2971 63 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 197 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 197 287 (accept_3_2 61 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 197 287 (Polychromatic418967fa.accept_22_16_21_1_1_17653 60
  197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 197 287
  (Polychromatic418967fa.accept_17_8_10_15_1_9328 59 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 197 287 (accept_3_2 58 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 197 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 197 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 197 287 (Polychromatic418967fa.accept_17_5_10_15_1_5574 56 197
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 197 287 (accept_3_2 55 197
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 197 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 197 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 197 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 287 (accept_3_2 52 197 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 197 287 (Polychromatic418967fa.accept_13_12_2_1_1_2909 51 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 197 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 197 287 (accept_3_2 49 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 197 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 48 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 197 287 (Polychromatic418967fa.accept_19_9_7_2_1_6868 47 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 197 287 (accept_3_2 46 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 197 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 197
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 287
  (Polychromatic418967fa.accept_20_4_17_7_1_3393 44 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 197 287 (accept_3_2 43 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 197 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 197 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 41 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 287 (accept_3_2 40 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 197 287 (Polychromatic418967fa.accept_17_5_10_15_1_5574 39 197
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 287 (accept_3_2 37 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 287 (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 287 (accept_3_2 34 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 287 (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 197
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 287
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 32 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 287 (accept_3_2 31 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 287 (accept_3_2 28 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 197
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 287 (accept_3_2 25 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 287 (Polychromatic418967fa.accept_19_4_7_2_1_6944 23 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 287 (accept_3_2 22 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 287 (Polychromatic418967fa.accept_17_4_10_15_1_5444 21 197
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 287
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 287 (accept_3_2 19 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 287 (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 287 (accept_3_2 16 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 287 (Polychromatic418967fa.accept_21_15_8_14_1_8860 15 197
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 287 (accept_3_2 13 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 287 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 287 (Polychromatic418967fa.accept_21_11_8_14_1_10515 11 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 287 (accept_3_2 10 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 197 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 287
  (Polychromatic418967fa.accept_14_8_1_7_1_3725 8 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 287 (accept_3_2 7 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 287 (Polychromatic418967fa.accept_17_5_10_15_1_5574 5 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 287 (accept_3_2 4 197 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 197 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 287 (accept_3_2 1 197 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 196 287
  (Eq.refl Bool.true) (allA_of_3_0 92 196 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 195 287 (Eq.refl
  Bool.true) (allA_succ_of_accept 92 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 195 287 (accept_3_2 91 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 195 287 (Polychromatic418967fa.accept_14_6_13_7_1_2015 90 195 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 195 287
  (Polychromatic418967fa.accept_25_14_20_12_1_8993 89 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 195 287 (accept_3_2 88 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 195 287 (Polychromatic418967fa.accept_16_7_3_15_1_2940 87 195 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 195 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 195 287 (accept_3_2 85 195 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 195 287 (Polychromatic418967fa.accept_8_4_3_7_1_491
  84 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 195 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 195 287 (accept_3_2 82 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 195 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 195 287 (accept_3_2 79 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 195 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 78 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 195 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 195 287 (accept_3_2 76 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 195 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 195 287 (accept_3_2 73 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 195 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 195 287
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 71 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 195 287 (accept_3_2 70 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 195 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 195 287 (accept_3_2 67 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 195 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 195 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 195 287 (accept_3_2 64 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 195 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 195 287 (accept_3_2 61 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 195 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 195 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 195 287 (accept_3_2 58 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 195 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 287 (accept_3_2 55 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 195 287 (Polychromatic418967fa.accept_19_16_5_2_1_8375 54 195 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 195 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 195 287 (accept_3_2 52 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 195 287 (Polychromatic418967fa.accept_21_9_6_14_1_7228 51 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 195 287 (accept_3_2 49 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 195 287 (accept_3_2 46 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 195 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 287 (accept_3_2 43 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 195 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 195 287 (accept_3_2 40 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 195 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 287 (accept_3_2 37 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 287
  (Polychromatic418967fa.accept_19_16_5_2_1_8375 35 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 195 287 (accept_3_2 34 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 195 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 287 (accept_3_2 31 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 287 (accept_3_2 28 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 195 287 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 287 (accept_3_2 25 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 287 (Polychromatic418967fa.accept_18_6_15_17_1_7363 24 195 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 287 (accept_3_2 22 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 195 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 287 (accept_3_2 19 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 287
  (Polychromatic418967fa.accept_19_17_5_2_1_2843 17 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 287 (accept_3_2 16 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 195 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 287 (accept_3_2 13 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 287 (accept_3_2 10 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 287 (accept_3_2 7 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 287 (Polychromatic418967fa.accept_14_6_13_7_1_2015 6 195 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 287 (accept_3_2 4 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 195 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 287 (accept_3_2 1 195 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 195
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 194
  287 (Eq.refl Bool.true) (allA_succ_of_accept 93 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 194 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 194 287 (accept_3_2 91 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 194 287 (Polychromatic418967fa.accept_17_5_7_15_1_1230 90 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 194 287 (accept_3_2 88 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 194 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 194 287
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 86 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 194 287 (accept_3_2 85 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 194 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 194 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 194 287 (accept_3_2 82 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 194 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 194 287 (accept_3_2 79 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 194 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 194 287 (accept_3_2 76 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 194 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 194 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 194 287 (accept_3_2 73 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 194 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 194 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 71 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 194 287 (accept_3_2 70 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 194 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 194 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 194 287 (accept_3_2 67 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 194 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 194 287 (accept_3_2 64 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 194 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 194 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 62 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 194 287 (accept_3_2 61 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 194 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 194 287 (Polychromatic418967fa.accept_21_17_5_14_1_4144 59 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 194 287 (accept_3_2 58 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 194 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 194 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 194 287 (accept_3_2 55 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 194 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 54 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 194 287 (accept_3_2 52 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 194 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 194 287
  (Polychromatic418967fa.accept_11_6_7_1_1_564 50 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 194 287 (accept_3_2 49 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 194 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 194 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 194 287 (accept_3_2 46 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 194 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 194 287 (accept_3_2 43 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 194 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 194 287 (accept_3_2 40 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 194 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 194 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 194 287 (accept_3_2 37 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 194 287 (Polychromatic418967fa.accept_17_2_7_15_1_5525 36 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 194 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 194 287 (accept_3_2 34 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 194 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 194 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 194 287 (accept_3_2 31 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 194 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 287 (accept_3_2 28 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 194 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 194 287
  (Polychromatic418967fa.accept_17_9_7_15_1_4346 26 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 194 287 (accept_3_2 25 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 194 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 194 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 194 287 (accept_3_2 22 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 194 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 194 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 194 287 (accept_3_2 19 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 194 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 194 287 (accept_3_2 16 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 194 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 194 287
  (Polychromatic418967fa.accept_19_14_4_2_1_2840 14 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 194 287 (accept_3_2 13 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 194 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 194 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 287 (accept_3_2 10 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 287 (accept_3_2 7 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 287 (accept_3_2 4 194 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 194 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 287 (accept_3_2 1 194 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 193
  287 (Eq.refl Bool.true) (allA_of_3_0 95 193 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 192 287
  (Eq.refl Bool.true) (allA_succ_of_accept 95 192 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 192 287 (accept_3_2 94 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 192 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 93 192
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 192 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 192 287 (accept_3_2 91 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 192 287 (Polychromatic418967fa.accept_21_6_3_14_1_11869 90 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 192 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 89 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 192 287 (accept_3_2 88 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 192 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 192 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 192 287 (accept_3_2 85 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 192 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 84 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 192 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 192 287 (accept_3_2 82 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 192 287 (Polychromatic418967fa.accept_14_11_10_7_1_1948 81 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 192 287
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 80 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 192 287 (accept_3_2 79 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 192 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 192 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 192 287 (accept_3_2 76 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 192 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 75 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 192 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 192 287 (accept_3_2 73 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 192 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 192 287 (Polychromatic418967fa.accept_21_8_3_14_1_4165 71 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 192 287 (accept_3_2 70 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 192 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 192 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 192 287 (accept_3_2 67 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 192 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 66 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 192 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 192 287 (accept_3_2 64 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 192 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 63 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 192 287
  (Polychromatic418967fa.accept_17_11_5_15_1_8144 62 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 192 287 (accept_3_2 61 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 192 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 192 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 192 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 192 287 (accept_3_2 58 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 192 287
  (Polychromatic418967fa.accept_20_17_12_7_1_4759 57 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 192 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 192 287 (accept_3_2 55 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 192 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 192 287
  (Polychromatic418967fa.accept_14_11_10_7_1_1948 53 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 192 287 (accept_3_2 52 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 192 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 192 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 192 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 192 287 (accept_3_2 49 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 192 287
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 48 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 192 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 192 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 192 287 (accept_3_2 46 192 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 192 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 192 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 192 287 (accept_3_2 43 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 192 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 192 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 287 (accept_3_2 40 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 192 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 192 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 192 287 (accept_3_2 37 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 192 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 192 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 287 (accept_3_2 34 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 192 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 192 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 192 287 (accept_3_2 31 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 192 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 192 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 287 (accept_3_2 28 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 192 287 (Polychromatic418967fa.accept_17_10_5_15_1_4332 27 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 192 287
  (Polychromatic418967fa.accept_20_6_12_7_1_12130 26 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 192 287 (accept_3_2 25 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 192 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 192 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 192 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 287 (accept_3_2 22 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 192 287
  (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 192 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 192 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 192 287 (accept_3_2 19 192 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 192 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 192 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 192 287 (accept_3_2 16 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 192 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 192 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 287 (accept_3_2 13 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 287 (Polychromatic418967fa.accept_21_12_3_14_1_10498 12 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 192 287 (accept_3_2 10 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  192 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 192 287 (Polychromatic418967fa.accept_21_8_3_14_1_4165 8 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 287 (accept_3_2 7 192 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 192 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 192 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 192 287 (accept_3_2 4 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  192 287 (Polychromatic418967fa.accept_14_3_10_7_1_3773 3 192 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 192 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 287 (accept_3_2 1 192 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 192
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 191
  287 (Eq.refl Bool.true) (allA_succ_of_accept 96 191 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 191 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 191 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 191 287 (accept_3_2 94 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 191 287 (Polychromatic418967fa.accept_18_2_11_17_1_4773 92 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 191 287 (accept_3_2 91 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 191 287 (Polychromatic418967fa.accept_19_14_1_2_1_11172 90 191
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 191 287
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 89 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 191 287 (accept_3_2 88 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 191 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 191 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 86 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 191 287 (accept_3_2 85 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 191 287
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 83 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 191 287 (accept_3_2 82 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 191 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 81 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 191 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 80 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 191 287 (accept_3_2 79 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 191 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 191 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 191 287 (accept_3_2 76 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 191 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 74 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 191 287 (accept_3_2 73 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 191 287 (Polychromatic418967fa.accept_14_2_9_7_1_5633 72 191
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 191 287
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 71 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 191 287 (accept_3_2 70 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 191 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 191 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 191 287 (accept_3_2 67 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 191 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 191 287 (accept_3_2 64 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 191 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 191 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 62 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 191 287 (accept_3_2 61 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 191 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 191 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 191 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 191 287 (accept_3_2 58 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 191 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 56 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 191 287 (accept_3_2 55 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 191 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 191
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 191 287
  (Polychromatic418967fa.accept_17_2_4_15_1_5451 53 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 191 287 (accept_3_2 52 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 191 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 191 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 191 287 (accept_3_2 49 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 191 287
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 47 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 191 287 (accept_3_2 46 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 191 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 191 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 44 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 191 287 (accept_3_2 43 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 191 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 191 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 191 287 (accept_3_2 40 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 191 287 (Polychromatic418967fa.accept_18_2_11_17_1_4773 38 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 287 (accept_3_2 37 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 191
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 287 (accept_3_2 34 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 287 (accept_3_2 31 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 287
  (Polychromatic418967fa.accept_21_8_2_14_1_10496 29 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 191 287 (accept_3_2 28 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 191 287 (Polychromatic418967fa.accept_17_10_4_15_1_2165 27 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 287 (Polychromatic418967fa.accept_10_6_1_7_1_342
  26 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 287 (accept_3_2 25
  191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 191 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 191 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 287 (accept_3_2 22 191 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 287 (accept_3_2 19 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 287 (Polychromatic418967fa.accept_21_17_2_14_1_7208 17 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 287 (accept_3_2 16 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 191 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 287 (accept_3_2 13 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 287 (accept_3_2 10 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 191
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 287 (accept_3_2 7 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 287 (accept_3_2 4 191 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 191 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 287
  (Polychromatic418967fa.accept_13_2_9_1_1_67 2 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 287 (accept_3_2 1 191 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  190 287 (Eq.refl Bool.true) (allA_of_3_0 98 190 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 189 287
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 189 287 7 14 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 189 287 (accept_3_2 97 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 189 287 (Polychromatic418967fa.accept_19_1_18_2_1_2835 96 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 189 287
  (Polychromatic418967fa.accept_17_10_2_15_1_3179 95 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 189 287 (accept_3_2 94 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 189 287 (Polychromatic418967fa.accept_25_18_14_12_1_8990 93 189 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 189 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 92
  189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 189 287 7 13 27 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 189 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 189 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 89 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 189 287 (accept_3_2 88 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 189 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 87 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 189 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 189 287 (accept_3_2 85 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84
  189 287 7 12 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 189 287 (Polychromatic418967fa.accept_15_8_9_2_1_1897 83 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 189 287 (accept_3_2 82 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 189 287 (Polychromatic418967fa.accept_13_3_7_1_1_334 81 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 189 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 189 287 (accept_3_2 79 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 77 189 287 7 11 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 189 287 (accept_3_2 76 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 189 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 189 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 189 287 (accept_3_2 73 189 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 189 287 (Polychromatic418967fa.accept_10_2_9_7_1_720
  72 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 189 287
  (Polychromatic418967fa.accept_13_6_7_1_1_335 71 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 189 287 7 10 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 189 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 69 189 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 189 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68
  189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 189 287 (accept_3_2 67
  189 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 189 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 189 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 287 (accept_3_2 64 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 189 287 7 9 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 189 287 (accept_3_2 61 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 189 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 60 189
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 189 287
  (Polychromatic418967fa.accept_25_9_14_12_1_17652 59 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 189 287 (accept_3_2 58 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 189 287 (Polychromatic418967fa.accept_20_17_9_7_1_13576 57 189 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 189 287 7 8 27 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 189 287 (accept_3_2 55 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 189 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 189 287
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 53 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 189 287 (accept_3_2 52 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 189 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 189 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 189 287 7 7 27 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 189 287
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 189 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 287 (accept_3_2 46 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 189 287 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 189 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 189 287 (accept_3_2 43 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  189 287 7 6 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 189 287 (Polychromatic418967fa.accept_15_11_9_2_1_4780 41 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 189 287 (accept_3_2 40 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 189 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 189 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 287 (accept_3_2 37 189 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 287 (Polychromatic418967fa.accept_11_3_2_1_1_994
  36 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 189 287 7 5 27 41
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 189 287
  (accept_3_2 34 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 287
  (Polychromatic418967fa.accept_18_15_9_17_1_6043 33 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 189 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 287 (accept_3_2 31 189 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 287
  (Polychromatic418967fa.accept_13_3_7_1_1_334 29 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 189 287 7 4 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 189 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 189 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 287 (accept_3_2 25 189 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 287
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 189 287 (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 287 (accept_3_2 22 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 189 287 7 3 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 189 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 287 (accept_3_2 19 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 189 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 287
  (Polychromatic418967fa.accept_20_17_9_7_1_13576 17 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 189 287 (accept_3_2 16 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 189 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 189 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 189 287 7 2 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 189 287 (accept_3_2 13 189 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 189 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 287
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 287 (accept_3_2 10 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 287 (Polychromatic418967fa.accept_19_9_18_2_1_8383 9 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 189 287 7 1 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 287
  (Polychromatic418967fa.accept_19_5_18_2_1_5404 5 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 287 (accept_3_2 4 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 189 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 189 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 287 (accept_3_2 1 189 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 189
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  188 287 (Eq.refl Bool.true) (allA_succ_of_accept 99 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 188 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 188 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 98 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 188 287 (accept_3_2 97 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 188 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 96 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 188 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 95 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 188 287 (accept_3_2 94 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 188 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 188 287
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 92 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 188 287 (accept_3_2 91 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 188 287 (Polychromatic418967fa.accept_19_14_17_2_1_1720 90 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 188 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 89 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 188 287 (accept_3_2 88 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 188 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 188 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 86 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 188 287 (accept_3_2 85 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 188 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 84 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 188 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 188 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 188 287 (accept_3_2 82 188 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 188 287
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 80 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 188 287 (accept_3_2 79 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 188 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 78 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 188 287 (Polychromatic418967fa.accept_16_13_12_15_1_6290 77 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 188 287 (accept_3_2 76 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 188 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 188 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 188 287 (accept_3_2 73 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 188 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 72 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 188 287 (Polychromatic418967fa.accept_14_1_6_7_1_1936 71 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 188 287 (accept_3_2 70 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 188 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 188 287
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 68 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 188 287 (accept_3_2 67 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 188 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 66 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 188 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 65 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 188 287 (accept_3_2 64 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 188 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 188 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 188 287 (accept_3_2 61 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 188 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 188 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 188 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 188 287 (accept_3_2 58 188 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 188 287
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 56 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 188 287 (accept_3_2 55 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 188 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 188 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 188 287 (Polychromatic418967fa.accept_19_15_17_2_1_4097 53 188
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 188 287 (accept_3_2 52 188
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 188 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 51 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 188 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 188 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 188 287 (accept_3_2 49 188 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 188 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 48 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 188 287
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 47 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 188 287 (accept_3_2 46 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 188 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 44 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 188 287 (accept_3_2 43 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 188 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 188
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 188 287
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 188 287 (accept_3_2 40 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 188 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 188 287 (accept_3_2 37 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 188 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 188
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 188 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 188 287 (accept_3_2 34 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 188 287 (Polychromatic418967fa.accept_21_11_20_14_1_4179 32 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 188 287 (accept_3_2 31 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 188 287 (Polychromatic418967fa.accept_20_10_8_7_1_7834 30 188
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 188 287
  (Polychromatic418967fa.accept_10_9_8_7_1_714 29 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 188 287 (accept_3_2 28 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 188 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 188 287 (accept_3_2 25 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 188 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 24 188
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 188 287
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 188 287 (accept_3_2 22 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 188 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 20 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 188 287 (accept_3_2 19 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 188 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 188
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 188 287
  (Polychromatic418967fa.accept_20_17_8_7_1_7859 17 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 188 287 (accept_3_2 16 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 188 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 188 287 (accept_3_2 13 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 188 287 (Polychromatic418967fa.accept_17_12_1_15_1_5472 12 188
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 188 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 188 287 (accept_3_2 10 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 188 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 188 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 188 287 (accept_3_2 7 188 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 188 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 188 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 188 287
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 188 287 (accept_3_2 4 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  188 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 188 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 188 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 188 287 (accept_3_2 1 188 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 187 287 (Eq.refl Bool.true) (allA_of_3_0 101 187 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 186
  287 (Eq.refl Bool.true) (allA_succ_of_accept 101 186 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 186 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 186 287 (accept_3_2 100 186 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 186 287
  (Polychromatic418967fa.accept_17_14_16_15_1_5509 99 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 186 287 (Polychromatic418967fa.accept_15_8_6_2_1_1128 98 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 186 287 (accept_3_2 97 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 186 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 96 186
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 186 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 186 287 (accept_3_2 94 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 186 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 186 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 92 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 186 287 (accept_3_2 91 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 186 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 186 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 186 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 186 287 (accept_3_2 88 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 186 287 (Polychromatic418967fa.accept_14_3_4_7_1_175 87 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 186 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 186 287 (accept_3_2 85 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 186 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 186 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 186 287 (accept_3_2 82 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 186 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 186 287 (Polychromatic418967fa.accept_14_10_4_7_1_1214 80 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 186 287 (accept_3_2 79 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 186 287 (Polychromatic418967fa.accept_16_14_10_15_1_3969 78
  186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 186 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 186 287 (accept_3_2 76 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 186 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 186 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 186 287 (accept_3_2 73 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 186 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 72 186 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 186 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 71 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 186 287 (accept_3_2 70 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 186 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 186 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 186 287 (accept_3_2 67 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 186 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 186 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 186 287 (accept_3_2 64 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 186 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 186 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 62 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 186 287 (accept_3_2 61 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 186 287 (Polychromatic418967fa.accept_23_14_2_11_1_11351 60
  186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 186 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 186 287 (accept_3_2 58 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 186 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 186 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 186 287 (accept_3_2 55 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 186 287 (Polychromatic418967fa.accept_21_12_18_14_1_8854 54 186 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 186 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 186 287 (accept_3_2 52 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 186 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 51 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 186 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 186 287 (accept_3_2 49 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 186 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 186 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 186 287 (accept_3_2 46 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 186 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 186 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 44 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 186 287 (accept_3_2 43 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 186 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 186
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 186 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 186 287 (accept_3_2 40 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 186 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 186 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 186 287 (accept_3_2 37 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 186 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 186 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 186 287
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 186 287 (accept_3_2 34 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 186 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 186 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 186 287 (accept_3_2 31 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 186 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 186 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 186 287 (accept_3_2 28 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 186 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 186 287 (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 186 287 (accept_3_2 25 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 186 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 186
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 186 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 186 287 (accept_3_2 22 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 186 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 186 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 287 (accept_3_2 19 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 186 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 186 287 (accept_3_2 16 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 186 287 (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 186 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 287 (accept_3_2 13 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 186 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 186 287 (accept_3_2 10 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  186 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 186 287 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 287 (accept_3_2 7 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 287 (Polychromatic418967fa.accept_19_6_15_2_1_2857 6 186 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 186 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 186 287 (accept_3_2 4 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  186 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 186 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 186 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 287 (accept_3_2 1 186 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 186
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 185 287 (Eq.refl Bool.true) (allA_succ_of_accept 102 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 185
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 185 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 101 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 185 287 (accept_3_2 100 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 185 287 (Polychromatic418967fa.accept_19_4_14_2_1_4117 99 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 185 287 (accept_3_2 97 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 185 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 185 287
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 95 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 185 287 (accept_3_2 94 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 185 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 185 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 185 287 (accept_3_2 91 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 185 287
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 89 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 185 287 (accept_3_2 88 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 185 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 185 287 (accept_3_2 85 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 185 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 185 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 185 287 (accept_3_2 82 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 185 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 81 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 185 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 80 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 185 287 (accept_3_2 79 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 185 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 185 287
  (Polychromatic418967fa.accept_19_1_14_2_1_4134 77 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 185 287 (accept_3_2 76 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 185 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 185 287 (accept_3_2 73 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 185 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 185 287
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 71 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 185 287 (accept_3_2 70 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 185 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 185 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 68 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 185 287 (accept_3_2 67 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 185 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 185 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 185 287 (accept_3_2 64 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 185 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 185 287 (accept_3_2 61 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 185 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 185 287
  (Polychromatic418967fa.accept_13_7_3_1_1_814 59 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 185 287 (accept_3_2 58 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 185 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 185 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 185 287 (accept_3_2 55 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 185 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 185 287 (accept_3_2 52 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 185 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 185 287 (accept_3_2 49 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 185 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 185 287 (accept_3_2 46 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 185 287 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 185 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 185 287 (accept_3_2 43 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 185 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 287
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 185 287 (accept_3_2 40 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 185 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 287 (accept_3_2 37 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 185 287 (Polychromatic418967fa.accept_19_17_14_2_1_4116 36 185 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 185 287
  (Polychromatic418967fa.accept_19_16_14_2_1_6924 35 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 185 287 (accept_3_2 34 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 185 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 185 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 185
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 185 287 (accept_3_2 31 185
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 185 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 185 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 185 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 287 (accept_3_2 28 185 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 185 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 287 (accept_3_2 25 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 287 (accept_3_2 22 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 185 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 287 (accept_3_2 19 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 287 (accept_3_2 16 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 185 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 287 (accept_3_2 13 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 287 (accept_3_2 10 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 287 (Polychromatic418967fa.accept_20_9_5_7_1_6336 9 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 287
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 287 (accept_3_2 7 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 287 (accept_3_2 4 185 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 185 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 287 (accept_3_2 1 185 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 184 287 (Eq.refl Bool.true) (allA_of_3_0 104 184 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 183
  287 (Eq.refl Bool.true) (allA_succ_of_accept 104 183 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 183 287 (accept_3_2 103 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 183 287
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 102 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 183 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 183 287 (accept_3_2 100 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 183 287 (Polychromatic418967fa.accept_16_3_7_15_1_1130 99 183
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 98 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 183 287 (accept_3_2 97 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 183 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 183 287 (accept_3_2 94 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 183 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 93 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 183 287 (accept_3_2 91 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 183 287 (Polychromatic418967fa.accept_14_6_1_7_1_2775 90 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 183 287 (Polychromatic418967fa.accept_15_14_3_2_1_2811 89 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 183 287 (accept_3_2 88 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 183 287 (accept_3_2 85 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 183 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 84 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 183 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 183 287 (accept_3_2 82 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 183 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 183 287 (accept_3_2 79 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 183 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 183 287 (accept_3_2 76 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 183 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 75 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 183 287 (accept_3_2 73 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 183 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 72 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 183 287 (Polychromatic418967fa.accept_19_14_12_2_1_6878 71 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 183 287 (accept_3_2 70 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 183 287 (accept_3_2 67 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 183 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 66 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 183 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 183 287 (accept_3_2 64 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 183 287 (Polychromatic418967fa.accept_19_6_12_2_1_8379 63 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 183 287 (accept_3_2 61 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 183 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 183 287 (accept_3_2 58 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 183 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 183 287 (accept_3_2 55 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 183 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 183 287 (Polychromatic418967fa.accept_17_2_13_15_1_4349 53 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 287 (accept_3_2 52 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 183 287 (accept_3_2 49 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 183 287 (Polychromatic418967fa.accept_14_6_1_7_1_2775 48 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 183 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 287 (accept_3_2 46 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 183 287 (accept_3_2 43 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 183 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 287 (accept_3_2 40 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 183 287 (accept_3_2 37 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 183 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 183 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 287 (accept_3_2 34 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 287 (accept_3_2 31 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 183 287 (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 183 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 287 (accept_3_2 28 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 287 (accept_3_2 25 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 183 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 287 (accept_3_2 22 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 287 (accept_3_2 19 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 183 287 (Polychromatic418967fa.accept_21_18_15_14_1_8871 18 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 287 (accept_3_2 16 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 183 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 287 (accept_3_2 13 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 183 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 183 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 287 (accept_3_2 10 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 287 (accept_3_2 7 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  183 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 183 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 287 (accept_3_2 4 183 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 287 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 183 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 287 (accept_3_2 1 183 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 182 287 (Eq.refl Bool.true) (allA_succ_of_gcd 105 182 287 7 15 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 182 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 104 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 182 287 (accept_3_2 103 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 182 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 182 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 182 287 (accept_3_2 100 182 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 182 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 182 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 182 287 7 14 26 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 182 287 (accept_3_2 97 182 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 182 287 (Polychromatic418967fa.accept_9_6_2_8_1_592
  96 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 182 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 182 287 (accept_3_2 94 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 182 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 92 182 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 182 287 7 13 26 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 182 287
  (Polychromatic418967fa.accept_22_2_6_1_1_17651 90 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 182 287 (accept_3_2 88 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 182 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 182 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 182 287 (Polychromatic418967fa.accept_9_5_2_8_1_109
  86 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 182 287 (accept_3_2 85
  182 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 182 287 7 12 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 182 287
  (Polychromatic418967fa.accept_18_11_2_17_1_3490 83 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 182 287 (accept_3_2 82 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 182 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 80 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 182 287 (accept_3_2 79 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 182 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 78 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 182 287 7 11 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 182 287 (accept_3_2 76 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 182 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 182 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 74 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 182 287 (accept_3_2 73 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 182 287
  (Polychromatic418967fa.accept_19_15_11_2_1_12506 72 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 182 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 182 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 182 287 7 10 26 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 182 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 182 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 182 287 (accept_3_2 67 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 182 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 182 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65
  182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 182 287 (accept_3_2 64
  182 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 182 287 7 9 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 182 287
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 62 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 182 287 (accept_3_2 61 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 182 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 182 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 182 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 182 287 (accept_3_2 58 182 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 182 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 182 287 7 8 26 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 182 287 (accept_3_2 55 182 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 182 287 (Polychromatic418967fa.accept_10_4_2_7_1_373
  54 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 182 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 182 287 (accept_3_2 52 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 182 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 182 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 182 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 182 287 7 7 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 182 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 48 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 182 287 (Polychromatic418967fa.accept_18_11_2_17_1_3490 47 182 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 182 287 (accept_3_2 46 182 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 182 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 182 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 182 287 (accept_3_2 43 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  182 287 7 6 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 182 287 (accept_3_2 40 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 182 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 182 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 182 287 (accept_3_2 37 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 182 287
  (Polychromatic418967fa.accept_23_13_21_11_1_6103 36 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 182 287 7 5 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 182 287 (accept_3_2 34 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 182 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 182 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 182 287 (accept_3_2 31 182 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 182 287 (Polychromatic418967fa.accept_9_3_2_8_1_108
  30 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 182 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 182 287 7 4 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 182 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 182 287 (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 182 287 (accept_3_2 25 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 182 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 182 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 287 (accept_3_2 22 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 182 287 7 3 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 182 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 182 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 182 287 (accept_3_2 19 182 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 182 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 182 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 182 287 (accept_3_2 16 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 182 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 182 287 7 2 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 182 287 (accept_3_2 13 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 182 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 182 287 (Polychromatic418967fa.accept_18_11_2_17_1_3490 11 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 287 (accept_3_2 10 182
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  9 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 182 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 182 287 7 1 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 182 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 182 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 182 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 182 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 287 (accept_3_2 4 182 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3
  182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 287
  (Polychromatic418967fa.accept_22_2_6_1_1_17651 2 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 182 287 (accept_3_2 1 182 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 181 287 (Eq.refl Bool.true) (allA_of_3_0 107 181 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 180 287 (Eq.refl Bool.true) (allA_succ_of_accept 107 180 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 107 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 180 287 (accept_3_2 106 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 180 287 (Polychromatic418967fa.accept_24_9_12_23_1_17650 105 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 180 287 (Polychromatic418967fa.accept_16_8_4_15_1_2941 104 180 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 180 287 (accept_3_2 103 180 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 180 287
  (Polychromatic418967fa.accept_19_7_9_2_1_4090 102 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 180 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 101 180 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 180 287 (accept_3_2 100 180 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 180 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 99 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 180 287
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 98 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 180 287 (accept_3_2 97 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 180 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 96 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 180 287 (Polychromatic418967fa.accept_21_11_12_14_1_5670 95 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 180 287 (accept_3_2 94 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 180 287 (Polychromatic418967fa.accept_14_9_12_7_1_597 93 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 180 287
  (Polychromatic418967fa.accept_16_12_4_15_1_5091 92 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 180 287 (accept_3_2 91 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 180 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 90 180 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 180 287
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 89 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 180 287 (accept_3_2 88 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 180 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 87 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 180 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 86 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 180 287 (accept_3_2 85 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 180 287 (Polychromatic418967fa.accept_23_15_19_11_1_14527 84
  180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 180 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 83 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 180 287 (accept_3_2 82 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 180 287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 81 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 180 287 (Polychromatic418967fa.accept_19_4_9_2_1_8342 80 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 180 287 (accept_3_2 79 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 180 287 (Polychromatic418967fa.accept_16_14_4_15_1_3944 78 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 180 287
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 77 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 180 287 (accept_3_2 76 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 180 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 180 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 180 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 74 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 180 287 (accept_3_2 73 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 180 287
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 180 287 (Polychromatic418967fa.accept_21_8_12_14_1_10464 71 180 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 180 287 (accept_3_2 70 180 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 180 287 (Polychromatic418967fa.accept_16_5_4_15_1_1102 69 180 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 180 287
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 68 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 180 287 (accept_3_2 67 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 180 287 (Polychromatic418967fa.accept_21_3_12_14_1_8848 66 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 180 287 (Polychromatic418967fa.accept_14_9_12_7_1_597 65 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 180 287 (accept_3_2 64 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 180 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 180 287
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 62 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 180 287 (accept_3_2 61 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 180 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 180 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 180 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 180 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 180 287 (accept_3_2 58 180 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 180 287
  (Polychromatic418967fa.accept_21_15_12_14_1_7232 57 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 180 287 (Polychromatic418967fa.accept_16_8_4_15_1_2941 56 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 180 287 (accept_3_2 55 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 180 287 (Polychromatic418967fa.accept_23_8_19_11_1_6256 54 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 180 287
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 53 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 180 287 (accept_3_2 52 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 180 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 180 287 (Polychromatic418967fa.accept_19_12_9_2_1_11136 50 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 180 287 (accept_3_2 49 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 180 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 180 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 47 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 180 287 (accept_3_2 46 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 180 287 (Polychromatic418967fa.accept_19_7_9_2_1_4090 45 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 180 287 (Polychromatic418967fa.accept_14_2_12_7_1_617 44 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 180 287 (accept_3_2 43 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 180 287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 180 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 180 287 (accept_3_2 40 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 180 287 (Polychromatic418967fa.accept_17_5_10_15_1_5574 39 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 180 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 38 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 180 287 (accept_3_2 37 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 180 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 180 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 180 287 (accept_3_2 34 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 180 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 33 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 180 287 (Polychromatic418967fa.accept_21_11_12_14_1_5670 32 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 287 (accept_3_2 31 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 180 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 180 287
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 29 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 180 287 (accept_3_2 28 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 180 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 180 287 (Polychromatic418967fa.accept_19_7_9_2_1_4090 26 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 180 287 (accept_3_2 25 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 180 287 (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 180 287
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 180 287 (accept_3_2 22 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 180 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 180 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 180 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 287 (accept_3_2 19 180
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 287
  (Polychromatic418967fa.accept_19_18_9_2_1_9764 18 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 180 287 (Polychromatic418967fa.accept_19_17_9_2_1_12492 17 180 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 287 (accept_3_2 16 180 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 180 287 (Polychromatic418967fa.accept_19_15_9_2_1_8347 15 180 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 180 287
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 14 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 180 287 (accept_3_2 13 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 180 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 180 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 287 (Polychromatic418967fa.accept_8_3_4_7_1_475
  11 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 180 287 (accept_3_2 10
  180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 180 287
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 180 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 180 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 287 (accept_3_2 7 180 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 180 287 (Polychromatic418967fa.accept_21_6_12_14_1_5704 6 180 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 287
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 5 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 180 287 (accept_3_2 4 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  180 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 180 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 180 287 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 180 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 287 (accept_3_2 1 180 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 180
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_287_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


