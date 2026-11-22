-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch283
-- name    : Polychromatic418967fa_Branch283
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:35:37.079072+00:00
-- url     : https://prove2.me/theorems/6895f884-1a65-4ebd-a8d3-31ba3efc3626
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch283_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_283 : allB 283 283 :=
  allB_succ' 2 282 283 (Eq.refl Bool.true) (allA_succ_of_accept 1 282 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  282 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 282 283)) (allB_succ' 3 281 283
  (Eq.refl Bool.true) (allA_of_3_1 3 281 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 280 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 280 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 280 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 280 283 (accept_3_3 2 280 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 280 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 280 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 280 283)))) (allB_succ' 5 279 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 279 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 279 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 279 283 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 279
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 279 283 (accept_3_3 2 279 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 279 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  1 279 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 279 283))))) (allB_succ' 6 278 283
  (Eq.refl Bool.true) (allA_of_3_1 6 278 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 277 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 277 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 277 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 277 283 (accept_3_3 5 277 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 277 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 277 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 277 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 277 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 277 283 (accept_3_3 2 277 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  277 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 277 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 277 283))))))) (allB_succ' 8 276 283 (Eq.refl Bool.true) (allA_succ_of_accept 7 276 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 276 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 276 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 6 276 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 276 283 (accept_3_3 5 276 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 276 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 276 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 276 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  276 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 276 283 (accept_3_3 2 276
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 276 283 (Polychromatic418967fa.accept_9_1_6_4_1_49
  1 276 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 276 283)))))))) (allB_succ' 9 275 283
  (Eq.refl Bool.true) (allA_of_3_1 9 275 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 274 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 274 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 274 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 274 283 (accept_3_3 8 274 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 274 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 274 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 274 283
  (Polychromatic418967fa.accept_15_6_4_13_1_403 6 274 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 274 283 (accept_3_3 5 274 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  274 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 274 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 274 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 274 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 274 283 (accept_3_3 2 274 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 274 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 274 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 274 283)))))))))) (allB_succ' 11 273 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 10 273 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 273 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 273 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686
  9 273 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 273 283 (accept_3_3 8
  273 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 273 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 273 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 273 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 273 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 273 283 (accept_3_3 5 273 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 273 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 273 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 273 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 3
  273 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 273 283 (accept_3_3 2 273
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 273 283 (Polychromatic418967fa.accept_9_1_3_4_1_47
  1 273 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 273 283))))))))))) (allB_succ' 12 272
  283 (Eq.refl Bool.true) (allA_of_3_1 12 272 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 271 283
  (Eq.refl Bool.true) (allA_succ_of_accept 12 271 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 271 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 271 283 (accept_3_3 11 271 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 271 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 271
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 271 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 271 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 271 283 (accept_3_3 8 271 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  271 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 271 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 271 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 271 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 271 283 (accept_3_3 5 271 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 271 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 271 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 271 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 271 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 271 283 (accept_3_3 2 271 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  271 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 271 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 271 283))))))))))))) (allB_succ' 14 270 283 (Eq.refl Bool.true) (allA_succ_of_accept 13 270 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 270 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 270 283 (Polychromatic418967fa.accept_20_12_10_3_1_4537 12 270 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 270 283 (accept_3_3 11 270 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 270 283 (Polychromatic418967fa.accept_19_10_4_17_1_1544 10 270 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 270 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 270 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 270 283 (accept_3_3 8 270 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  270 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 270 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 270 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 270 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 270 283 (accept_3_3 5 270 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 270 283 (Polychromatic418967fa.accept_17_4_15_11_1_6465 4 270 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 270 283
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 270 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 270 283 (accept_3_3 2 270 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  270 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 270 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 270 283)))))))))))))) (allB_succ' 15 269 283 (Eq.refl Bool.true) (allA_of_3_1 15 269 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 268 283 (Eq.refl Bool.true) (allA_succ_of_accept 15 268 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 268 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 268 283 (accept_3_3 14 268 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 268 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 268 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 268 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 268 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 268 283 (accept_3_3 11 268 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 268 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 268 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 268 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 268 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 268 283 (accept_3_3 8 268 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  268 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 268 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 268 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 268 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 268 283 (accept_3_3 5 268 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 268 283 (Polychromatic418967fa.accept_13_4_8_10_1_671 4 268 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 268 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 268 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 268 283 (accept_3_3 2 268 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  268 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 268 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 268 283)))))))))))))))) (allB_succ' 17 267 283 (Eq.refl Bool.true) (allA_succ_of_accept 16 267
  283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 267 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 267 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 267 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 267 283 (accept_3_3 14 267 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 267 283 (Polychromatic418967fa.accept_17_13_12_11_1_2947 13 267 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 267 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 267 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 267 283 (accept_3_3 11 267 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 267 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 267 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 267 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 267 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 267 283 (accept_3_3 8 267 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 267 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 267 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 267 283
  (Polychromatic418967fa.accept_10_6_7_3_1_547 6 267 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 267 283 (accept_3_3 5 267 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  267 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 267 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 267 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 267 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 267 283 (accept_3_3 2 267 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 267 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 267 283))))))))))))))))) (allB_succ' 18 266 283 (Eq.refl
  Bool.true) (allA_of_3_1 18 266 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 265 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 265 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 265 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 265 283 (accept_3_3 17 265 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 265 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 265 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 265 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  15 265 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 265 283 (accept_3_3 14
  265 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 265 283
  (Polychromatic418967fa.accept_19_13_18_17_1_5141 13 265 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 265 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 265 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 265 283 (accept_3_3 11 265 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 265 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 265 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 265 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 265 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 265 283 (accept_3_3 8 265 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  265 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 265 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 265 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 265 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 265 283 (accept_3_3 5 265 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 265 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 265 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 265 283
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 3 265 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 265 283 (accept_3_3 2 265 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  265 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 265 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 265 283))))))))))))))))))) (allB_succ' 20 264 283 (Eq.refl Bool.true) (allA_succ_of_accept 19
  264 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 264 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 264 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 264 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 264 283 (accept_3_3 17 264 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 264 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 264 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 264 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 264 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 264 283 (accept_3_3 14 264 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 264 283 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 264 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 264 283 (Polychromatic418967fa.accept_16_12_8_11_1_2695 12 264 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 264 283 (accept_3_3 11 264 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 264 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 264 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 264 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 264 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 264 283 (accept_3_3 8 264 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  264 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 264 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 264 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 264 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 264 283 (accept_3_3 5 264 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 264 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 4 264 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 264 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 264 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 264 283 (accept_3_3 2 264 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  264 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 264 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 264 283)))))))))))))))))))) (allB_succ' 21 263 283 (Eq.refl Bool.true) (allA_of_3_1 21 263 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 262 283 (Eq.refl Bool.true) (allA_succ_of_accept 21 262 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 262 283 (accept_3_3 20 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 262 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 262 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 262 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 262 283 (accept_3_3 17 262 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 262 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 262 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 262 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 262 283 (accept_3_3 14 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 262 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 262 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 262 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 262 283 (accept_3_3 11 262 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 262 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 262 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 262 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 262 283 (accept_3_3 8 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  262 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 262 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 262 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 262 283 (accept_3_3 5 262 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 262 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 262 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 262 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 262 283 (accept_3_3 2 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  262 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 262 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 262 283)))))))))))))))))))))) (allB_succ' 23 261 283 (Eq.refl Bool.true) (allA_succ_of_accept 22
  261 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 261 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 261 283 (Polychromatic418967fa.accept_17_4_6_11_1_1030 21 261 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 261 283 (accept_3_3 20 261 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 261 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 261 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 261 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 261 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 261 283 (accept_3_3 17 261 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 261 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 261 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 261 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 261 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 261 283 (accept_3_3 14 261 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 261 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 261 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 261 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 261 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 261 283 (accept_3_3 11 261 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 261 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 261 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 261 283 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 261 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 261 283 (accept_3_3 8 261 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 261 283 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 261 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 261 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 261 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 261 283 (accept_3_3 5 261 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  261 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 261 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 261 283 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 261 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 261 283 (accept_3_3 2 261 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 261 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 261 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 261 283))))))))))))))))))))))) (allB_succ' 24 260 283
  (Eq.refl Bool.true) (allA_of_3_1 24 260 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 259 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 259 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 259 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 259 283 (accept_3_3 23 259 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 259 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 22 259 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 259 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 259 283 (accept_3_3 20 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 259 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 259 283 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 259 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 259 283 (accept_3_3 17 259 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 259 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 259
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 259 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 259 283 (accept_3_3 14 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 259 283 (Polychromatic418967fa.accept_21_13_7_10_1_8599 13 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 259 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 259 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 259 283 (accept_3_3 11 259 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 259 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 259 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 259 283
  (Polychromatic418967fa.accept_13_9_12_10_1_242 9 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 259 283 (accept_3_3 8 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  259 283 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 259 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 259 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 259 283 (accept_3_3 5 259 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 259 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 259 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 259 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 259 283 (accept_3_3 2 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  259 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 259 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 259 283))))))))))))))))))))))))) (allB_succ' 26 258 283 (Eq.refl Bool.true) (allA_succ_of_accept
  25 258 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 258 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 258 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 258 283 (accept_3_3 23 258 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 258 283 (Polychromatic418967fa.accept_16_6_2_11_1_7132 22 258
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 258 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 258 283 (accept_3_3 20 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 258 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 258 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 258 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 258 283 (accept_3_3 17 258 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 258 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 258 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 258 283
  (Polychromatic418967fa.accept_10_5_8_3_1_229 15 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 258 283 (accept_3_3 14 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 258 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 258 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 258 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 258 283 (accept_3_3 11 258 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 258 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 258 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 258 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 258 283 (accept_3_3 8 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  258 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 258 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 258 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 258 283 (accept_3_3 5 258 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 258 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 258 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 258 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 258 283 (accept_3_3 2 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  258 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 258 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 258 283)))))))))))))))))))))))))) (allB_succ' 27 257 283 (Eq.refl Bool.true) (allA_of_3_1 27 257
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 256 283 (Eq.refl Bool.true) (allA_succ_of_accept 27 256
  283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 256 283 (accept_3_3 26 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 256 283 (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 256 283 (Polychromatic418967fa.accept_17_7_1_11_1_1894 24 256 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 256 283 (accept_3_3 23 256 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 256 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 256 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 256 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 256 283 (accept_3_3 20 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 256 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 256 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 256 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 256 283 (accept_3_3 17 256 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 256 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 256
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 256 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 256 283 (accept_3_3 14 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 256 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 256 283 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 256 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 256 283 (accept_3_3 11 256 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 256 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 256
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 256 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 256 283 (accept_3_3 8 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  256 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 256 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 256 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 256 283 (accept_3_3 5 256 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 256 283 (Polychromatic418967fa.accept_23_4_3_7_1_15880 4 256 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 256 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 256 283 (accept_3_3 2 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  256 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 256 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 256 283)))))))))))))))))))))))))))) (allB_succ' 29 255 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 255 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 255 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 255 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 255
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 255 283 (accept_3_3 26 255
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 255 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 255 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 255 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 255 283 (accept_3_3 23 255 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 255 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 255 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 255 283 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 255 283 (accept_3_3 20
  255 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 255 283
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 255 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 255 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 255 283 (accept_3_3 17 255 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 255 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 255 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 255 283 (Polychromatic418967fa.accept_9_6_3_4_1_477
  15 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 255 283 (accept_3_3 14
  255 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 255 283
  (Polychromatic418967fa.accept_21_13_3_10_1_2592 13 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 255 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 255 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 255 283 (accept_3_3 11 255 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 255 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 255 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 255 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 255 283 (accept_3_3 8 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  255 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 255 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 255 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 255 283 (accept_3_3 5 255 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 255 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 255 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 283
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 3 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 255 283 (accept_3_3 2 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  255 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 255 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 255 283))))))))))))))))))))))))))))) (allB_succ' 30 254 283 (Eq.refl Bool.true) (allA_of_3_1 30
  254 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 253 283 (Eq.refl Bool.true) (allA_succ_of_accept 30
  253 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 253 283 (accept_3_3 29 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 253 283 (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 253 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 253 283 (Polychromatic418967fa.accept_19_8_6_17_1_5186 27 253
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 253 283 (accept_3_3 26 253
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 253 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 253 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 253 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 253 283 (accept_3_3 23 253 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 253 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 253 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 253 283 (Polychromatic418967fa.accept_9_3_1_4_1_216
  21 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 253 283 (accept_3_3 20
  253 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 253 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 253 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 253 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 253 283 (accept_3_3 17 253 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 253 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 253 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 253 283 (Polychromatic418967fa.accept_9_6_1_4_1_474
  15 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 253 283 (accept_3_3 14
  253 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 253 283
  (Polychromatic418967fa.accept_17_13_15_11_1_2936 13 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 253 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 253 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 253 283 (accept_3_3 11 253 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 253 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 253 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 253 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 253 283 (accept_3_3 8 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  253 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 253 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 253 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 253 283 (accept_3_3 5 253 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 253 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 253 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 253 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 253 283 (accept_3_3 2 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  253 283 (Polychromatic418967fa.accept_20_1_13_3_1_11838 1 253 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 253 283))))))))))))))))))))))))))))))) (allB_succ' 32 252 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 252 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 252 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 252 283 (Polychromatic418967fa.accept_13_4_5_10_1_1247 30 252
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 252 283 (accept_3_3 29 252
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 252 283
  (Polychromatic418967fa.accept_13_2_5_10_1_250 28 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 252 283 (Polychromatic418967fa.accept_22_5_10_19_1_17384 27 252 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 252 283 (accept_3_3 26 252 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 252 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 252 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 252 283
  (Polychromatic418967fa.accept_16_8_12_11_1_3697 24 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 252 283 (accept_3_3 23 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 252 283 (Polychromatic418967fa.accept_19_3_5_17_1_9438 22 252 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 252 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 252
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 252 283 (accept_3_3 20 252
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 252 283
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 252 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 252 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 252 283 (accept_3_3 17 252 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 252 283 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 252 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 252 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 252 283 (accept_3_3 14 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 252 283 (Polychromatic418967fa.accept_20_13_12_3_1_5972 13 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 252 283 (Polychromatic418967fa.accept_17_12_14_11_1_998 12 252 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 252 283 (accept_3_3 11 252 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 252 283 (Polychromatic418967fa.accept_15_10_12_13_1_2585 10
  252 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 252 283
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 252 283 (accept_3_3 8 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  252 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 252 283 (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 252 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 252 283 (accept_3_3 5 252 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 252 283 (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 252
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 252 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 252 283 (accept_3_3 2 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  252 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 252 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 252 283)))))))))))))))))))))))))))))))) (allB_succ' 33 251 283 (Eq.refl Bool.true) (allA_of_3_1
  33 251 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 250 283 (Eq.refl Bool.true) (allA_succ_of_accept 33
  250 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 250 283 (accept_3_3 32 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 250 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 250 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 250 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 250 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 250 283 (accept_3_3 29 250 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 250 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28
  250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 250 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 250 283 (accept_3_3 26 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 250 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 250 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 250 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 250 283 (accept_3_3 23 250 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 250 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 250 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 250 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 250 283 (accept_3_3 20 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 250 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 250 283 (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 250 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 250 283 (accept_3_3 17 250 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 250 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 250 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 250 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 250 283 (accept_3_3 14 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 250 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 250 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 250 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 250 283 (accept_3_3 11 250 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 250 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 250 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 250 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 250 283 (accept_3_3 8 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  250 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 250 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 250 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 250 283 (accept_3_3 5 250 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 250 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 250 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 250 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 250 283 (accept_3_3 2 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  250 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 250 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 250 283)))))))))))))))))))))))))))))))))) (allB_succ' 35 249 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 34 249 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 249 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 249 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 33 249
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 249 283 (accept_3_3 32 249
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 249 283
  (Polychromatic418967fa.accept_13_5_2_10_1_248 31 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 249 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 249 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 249 283 (accept_3_3 29 249 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 249 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 249 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 249 283 (Polychromatic418967fa.accept_7_6_4_3_1_266
  27 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 249 283 (accept_3_3 26
  249 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 249 283
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 249 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 249 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 249 283 (accept_3_3 23 249 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 249 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 249 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 249 283 (Polychromatic418967fa.accept_9_3_6_4_1_210
  21 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 249 283 (accept_3_3 20
  249 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 249 283
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 249 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 249 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 249 283 (accept_3_3 17 249 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 249 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 249 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 249 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 249 283 (accept_3_3 14
  249 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 249 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 249 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 249 283 (accept_3_3 11 249 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 249 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 249 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 249 283
  (Polychromatic418967fa.accept_19_9_2_17_1_10805 9 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 249 283 (accept_3_3 8 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  249 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 249 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 249 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 283 (accept_3_3 5 249 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 249 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 249 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 249 283 (accept_3_3 2 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  249 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 249 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 249 283))))))))))))))))))))))))))))))))))) (allB_succ' 36 248 283 (Eq.refl Bool.true)
  (allA_of_3_1 36 248 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 247 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 247 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 247 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 247 283 (accept_3_3 35 247 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 247 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 247 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 247 283 (Polychromatic418967fa.accept_7_5_2_3_1_106
  33 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 247 283 (accept_3_3 32
  247 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 247 283
  (Polychromatic418967fa.accept_16_15_7_11_1_3760 31 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 247 283 (Polychromatic418967fa.accept_20_10_7_3_1_16094 30 247 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 247 283 (accept_3_3 29 247 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 247 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 247 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 247 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 247 283 (accept_3_3 26 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 247 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 247 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 247 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 247 283 (accept_3_3 23 247 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 247 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 247 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 247 283
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 21 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 247 283 (accept_3_3 20 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 247 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 247 283 (Polychromatic418967fa.accept_16_2_7_11_1_1698 18 247 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 247 283 (accept_3_3 17 247 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 247 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 247
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 247 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 247 283 (accept_3_3 14 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 247 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 247 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 247 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 247 283 (accept_3_3 11 247 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 247 283 (Polychromatic418967fa.accept_20_10_7_3_1_16094 10 247 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 247 283
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 247 283 (accept_3_3 8 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  247 283 (Polychromatic418967fa.accept_21_7_16_10_1_1349 7 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 247 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 247 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 247 283 (accept_3_3 5 247 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 247 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 247 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 247 283
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 247 283 (accept_3_3 2 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  247 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 247 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 247 283))))))))))))))))))))))))))))))))))))) (allB_succ' 38 246 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 246 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 246 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 246 283 (Polychromatic418967fa.accept_16_4_6_11_1_3753 36 246
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 246 283 (accept_3_3 35 246
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 246 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 34 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 246 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 246 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 246 283 (accept_3_3 32 246 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 246 283 (Polychromatic418967fa.accept_17_14_8_11_1_4052 31 246 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 246 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 246 283 (accept_3_3 29 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 246 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 246 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 246 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 246 283 (accept_3_3 26 246 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 246 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 246 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 246 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 246 283 (accept_3_3 23 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 246 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 22 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 246 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 246 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 246 283 (accept_3_3 20 246 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 246 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 246 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 246 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 246 283 (accept_3_3 17 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 246 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 246 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 246 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 246 283 (accept_3_3 14 246 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 246 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 246 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 246 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 246 283 (accept_3_3 11 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 246 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 246 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 246 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 246 283 (accept_3_3 8 246 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 246 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 246 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 246 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 246 283 (accept_3_3 5 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  246 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 246 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 246 283 (Polychromatic418967fa.accept_16_3_6_11_1_2718 3 246 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 246 283 (accept_3_3 2 246 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 246 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246 283))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 245 283 (Eq.refl Bool.true) (allA_of_3_1 39 245 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 244 283 (Eq.refl Bool.true) (allA_succ_of_accept 39 244 283 (Polychromatic418967fa.accept_6_3_4_1_1_8
  39 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 244 283 (accept_3_3 38
  244 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 244 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 244 283 (Polychromatic418967fa.accept_15_6_4_13_1_403 36 244 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 244 283 (accept_3_3 35 244 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 244 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 244 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 244 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 244 283 (accept_3_3 32
  244 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 244 283
  (Polychromatic418967fa.accept_8_7_4_3_1_156 31 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 244 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 244 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 244 283 (accept_3_3 29 244 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 244 283 (Polychromatic418967fa.accept_16_12_4_11_1_3710 28 244 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 244 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 244 283 (accept_3_3 26 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 244 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 244 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 244 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 244 283 (accept_3_3 23 244 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 244 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 244 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 244 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 244 283 (accept_3_3 20 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 244 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 244 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 244 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 244 283 (accept_3_3 17 244 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 244 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 244 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 244 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 244 283 (accept_3_3 14 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 244 283 (Polychromatic418967fa.accept_17_13_6_11_1_4014 13 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 244 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 244 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 244 283 (accept_3_3 11 244 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 244 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 244 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 244 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 244 283 (accept_3_3 8 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  244 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 244 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 244 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 244 283 (accept_3_3 5 244 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 244 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 244 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 244 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 244 283 (accept_3_3 2 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  244 283 (Polychromatic418967fa.accept_18_1_10_13_1_500 1 244 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 244 283)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 243 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 243 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 243 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 243 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 243
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 243 283 (accept_3_3 38 243
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 243 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 243 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 243 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 243 283 (accept_3_3 35 243 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 243 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 243 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 243 283 (Polychromatic418967fa.accept_12_9_3_7_1_924
  33 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 243 283 (accept_3_3 32
  243 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 243 283
  (Polychromatic418967fa.accept_15_1_3_13_1_2548 31 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 243 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 243 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 243 283 (accept_3_3 29 243 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 243 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 243 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 243 283 (Polychromatic418967fa.accept_13_1_9_10_1_625
  27 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 243 283 (accept_3_3 26
  243 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 243 283
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 243 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 243 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 243 283 (accept_3_3 23 243 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 243 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 243 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 243 283 (accept_3_3 20 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 243 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 243 283 (Polychromatic418967fa.accept_22_18_1_19_1_6422 18 243 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 243 283 (accept_3_3 17 243 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 243 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 243 283 (accept_3_3 14 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 243 283 (Polychromatic418967fa.accept_19_13_15_17_1_5199 13 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 243 283 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 243 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 243 283 (accept_3_3 11 243 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 243 283 (accept_3_3 8 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  243 283 (Polychromatic418967fa.accept_16_7_3_11_1_3682 7 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 243 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 243 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 283 (accept_3_3 5 243 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 243 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 283
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 3 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 243 283 (accept_3_3 2 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  243 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 243 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 243 283))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 242 283 (Eq.refl Bool.true)
  (allA_of_3_1 42 242 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 241 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 42 241 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 241 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 241 283 (accept_3_3 41 241 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 241 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 241 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 241 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 241 283 (accept_3_3 38 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 241 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 241 283 (Polychromatic418967fa.accept_17_2_3_11_1_2919 36 241 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 241 283 (accept_3_3 35 241 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 241 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 241 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 241 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 241 283 (accept_3_3 32 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 241 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 241 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 241 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 241 283 (accept_3_3 29 241 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 241 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 241 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 241 283
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 241 283 (accept_3_3 26 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 241 283 (Polychromatic418967fa.accept_13_12_7_10_1_2662 25 241 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 241 283 (Polychromatic418967fa.accept_9_6_7_4_1_212
  24 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 241 283 (accept_3_3 23
  241 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 241 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 241 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 241 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 241 283 (accept_3_3 20 241 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 241 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 241 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 241 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 241 283 (accept_3_3 17
  241 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 241 283
  (Polychromatic418967fa.accept_13_3_7_10_1_668 16 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 241 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 241 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 241 283 (accept_3_3 14 241 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 241 283 (Polychromatic418967fa.accept_20_13_1_3_1_11831 13 241 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 241 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 241 283 (accept_3_3 11 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 241 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 241 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 241 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 283 (accept_3_3 8 241 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 283 (Polychromatic418967fa.accept_19_7_13_17_1_8041 7 241 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 241 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 283 (accept_3_3 5 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 283 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 241 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 241 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 283 (accept_3_3 2 241 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 241 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 283)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 240 283 (Eq.refl Bool.true) (allA_succ_of_accept 43 240 283 (Polychromatic418967fa.accept_7_1_2_3_1_257
  43 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 240 283
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 42 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 240 283 (accept_3_3 41 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 240 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 240 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 240 283 (accept_3_3 38 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 240 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 240 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 240 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 240 283 (accept_3_3 35 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 240 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 240 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 240 283 (accept_3_3 32 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 240 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 240 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 240 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 240 283 (accept_3_3 29 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 240 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 240 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 240 283 (accept_3_3 26 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 240 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 240 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 240 283
  (Polychromatic418967fa.accept_19_5_12_17_1_8089 24 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 240 283 (accept_3_3 23 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 240 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 240 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 240 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 240 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 240 283 (accept_3_3 20 240 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 240 283 (Polychromatic418967fa.accept_7_5_2_3_1_106
  19 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 240 283
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 240 283 (accept_3_3 17 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 240 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 240 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 240 283 (accept_3_3 14 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 240 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 240 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 240 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 240 283 (accept_3_3 11 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 240 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 240 283 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 240 283 (accept_3_3 8 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 240 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 240 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 240 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 240 283 (accept_3_3 5 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  240 283 (Polychromatic418967fa.accept_13_4_6_10_1_1199 4 240 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 240 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 240 283 (accept_3_3 2 240 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 240 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 283))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 239 283 (Eq.refl Bool.true) (allA_of_3_1 45 239 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 238 283 (Eq.refl Bool.true) (allA_succ_of_accept 45 238 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  45 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 238 283 (accept_3_3 44
  238 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 238 283
  (Polychromatic418967fa.accept_18_7_4_13_1_3315 43 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 238 283 (Polychromatic418967fa.accept_19_4_10_17_1_5194 42 238 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 238 283 (accept_3_3 41 238 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 238 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 238 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 238 283 (accept_3_3 38 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 238 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 238 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 238 283 (accept_3_3 35 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 238 283 (Polychromatic418967fa.accept_13_8_4_10_1_4358 34 238
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 238 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 238 283 (accept_3_3 32 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 238 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 238 283 (Polychromatic418967fa.accept_21_9_7_10_1_3907 30 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 238 283 (accept_3_3 29 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 238 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 238
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 238 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 238 283 (accept_3_3 26 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 238 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 238 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 238 283 (accept_3_3 23 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 238 283 (Polychromatic418967fa.accept_20_2_18_3_1_4519 22 238
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 238 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 238 283 (accept_3_3 20 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 238 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 238 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 238 283 (accept_3_3 17 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 238 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 238
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 238 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 238 283 (accept_3_3 14 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 238 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 238 283 (Polychromatic418967fa.accept_19_12_10_17_1_5189 12 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 238 283 (accept_3_3 11 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 238 283 (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 238
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 238 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 238 283 (accept_3_3 8 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  238 283 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 238 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 238 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 238 283 (accept_3_3 5 238 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 238 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 238 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 238 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 238 283 (accept_3_3 2 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  238 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 238 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 238 283)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 237 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 237 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 237 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 237
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 237 283 (accept_3_3 44 237
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 237 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 237 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 237 283 (accept_3_3 41 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 237 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 237 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 237 283 (Polychromatic418967fa.accept_7_4_6_3_1_271
  39 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 237 283 (accept_3_3 38
  237 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 237 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 237 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 237 283 (accept_3_3 35 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 237 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 237 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 237 283 (Polychromatic418967fa.accept_9_6_3_4_1_477
  33 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 237 283 (accept_3_3 32
  237 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 237 283
  (Polychromatic418967fa.accept_15_1_12_13_1_944 31 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 237 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 237 283 (accept_3_3 29 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 237 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 237 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 237 283 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 237 283 (accept_3_3 26
  237 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 237 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 237 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 237 283 (accept_3_3 23 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 237 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 237 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 283 (Polychromatic418967fa.accept_19_2_9_17_1_626
  21 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 237 283 (accept_3_3 20
  237 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 237 283
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 237 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 237 283 (accept_3_3 17 237 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 237 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 237 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 283 (Polychromatic418967fa.accept_9_6_3_4_1_477
  15 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 283 (accept_3_3 14
  237 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 283
  (Polychromatic418967fa.accept_19_13_9_17_1_8070 13 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 237 283 (Polychromatic418967fa.accept_17_12_16_11_1_7885 12 237 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 283 (accept_3_3 11 237 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 237 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 237 283 (accept_3_3 8 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  237 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 237 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 237 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 283 (accept_3_3 5 237 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 237 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 283
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 237 283 (accept_3_3 2 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  237 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 237 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 237 283))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 236 283 (Eq.refl
  Bool.true) (allA_of_3_1 48 236 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 235 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 235 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 235 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 235 283 (accept_3_3 47 235 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 235 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 46 235 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 235 283
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 235 283 (accept_3_3 44 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 235 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 235 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 235 283 (accept_3_3 41 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 235 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 235 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 235 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 235 283 (accept_3_3 38 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 235 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 235 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 235 283 (accept_3_3 35 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 235 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 235 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 235 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 235 283 (accept_3_3 32 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 235 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 235 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 235 283 (accept_3_3 29 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 235 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 235 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 235 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 235 283 (accept_3_3 26 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 235 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 235 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 235 283 (accept_3_3 23 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 235 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 235 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 235 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 235 283 (accept_3_3 20 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 235 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 235 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 235 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 235 283 (accept_3_3 17 235 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 235 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 235 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 235 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 235 283 (accept_3_3 14 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 235 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 235 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 235 283 (accept_3_3 11 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 235 283 (Polychromatic418967fa.accept_18_10_1_13_1_2192 10 235 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 235 283
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 235 283 (accept_3_3 8 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  235 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 235 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 235 283 (accept_3_3 5 235 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 235 283 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 235 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 235 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 235 283 (accept_3_3 2 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  235 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 235 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 235 283))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 234 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 234 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 234 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 234 283
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 234 283 (accept_3_3 47 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 234 283 (Polychromatic418967fa.accept_17_12_13_11_1_2910 46 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 234 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 234 283 (accept_3_3 44 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 234 283 (Polychromatic418967fa.accept_21_1_3_10_1_5401 43 234
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 234 283
  (Polychromatic418967fa.accept_19_4_6_17_1_12062 42 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 234 283 (accept_3_3 41 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 234 283 (Polychromatic418967fa.accept_17_6_13_11_1_995 40 234 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 234 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 234
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 234 283 (accept_3_3 38 234
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 234 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  37 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 234 283
  (Polychromatic418967fa.accept_21_15_3_10_1_8533 36 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 234 283 (accept_3_3 35 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 234 283 (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 234 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 234 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 234 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 234 283 (accept_3_3 32 234 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 234 283
  (Polychromatic418967fa.accept_16_15_10_11_1_1727 31 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 234 283 (Polychromatic418967fa.accept_19_11_6_17_1_9455 30 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 234 283 (accept_3_3 29 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 234 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 234
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 234 283
  (Polychromatic418967fa.accept_10_7_4_3_1_560 27 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 234 283 (accept_3_3 26 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 234 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 234 283 (Polychromatic418967fa.accept_17_7_13_11_1_2895 24 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 234 283 (accept_3_3 23 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 234 283 (Polychromatic418967fa.accept_15_7_9_13_1_3451 22 234
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 234 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 234 283 (accept_3_3 20 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 234 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 234 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 234 283 (accept_3_3 17 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 234 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 234
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 234 283
  (Polychromatic418967fa.accept_16_15_10_11_1_1727 15 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 234 283 (accept_3_3 14 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 234 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 234 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 234 283 (Polychromatic418967fa.accept_16_12_10_11_1_2667 12
  234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 283 (accept_3_3 11
  234 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 283
  (Polychromatic418967fa.accept_24_10_18_19_1_10748 10 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 234 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 234 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 234 283 (accept_3_3 8 234 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 234 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 234 283
  (Polychromatic418967fa.accept_11_6_3_8_1_843 6 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 234 283 (accept_3_3 5 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  234 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 4 234 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 234 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 234 283 (accept_3_3 2 234 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 234 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 234 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234
  283)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 233 283 (Eq.refl Bool.true) (allA_of_3_1 51 233
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 232 283 (Eq.refl Bool.true) (allA_succ_of_accept 51 232
  283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 232 283 (accept_3_3 50 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 232 283 (Polychromatic418967fa.accept_19_11_4_17_1_2617 49 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 232 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 232 283 (accept_3_3 47 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 232 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 232 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 232 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 232 283 (accept_3_3 44 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 232 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 43 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 232 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 232 283 (accept_3_3 41 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 232 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 232 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 232 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 232 283 (accept_3_3 38 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 232 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 232 283 (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 232 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 232 283 (accept_3_3 35 232 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 232 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 232
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 232 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 232 283 (accept_3_3 32 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 232 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 232 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 232 283 (accept_3_3 29 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 232 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 232 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 232 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 232 283 (accept_3_3 26 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 232 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 232 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 232 283 (accept_3_3 23 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 232 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 232 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 232 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 232 283 (accept_3_3 20 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 232 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 232 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 232 283 (accept_3_3 17 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 232 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 232 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 232 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 232 283 (accept_3_3 14 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 232 283 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 232 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 232 283 (accept_3_3 11 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 232 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 232 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 232 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 232 283 (accept_3_3 8 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  232 283 (Polychromatic418967fa.accept_21_7_1_10_1_8571 7 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 232 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 232 283 (accept_3_3 5 232 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 232 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 232 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 232 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 232 283 (accept_3_3 2 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  232 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 232 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 232 283)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 231 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 231 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 231 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 231 283
  (Polychromatic418967fa.accept_16_3_7_11_1_1723 51 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 231 283 (accept_3_3 50 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 231 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 49 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 231 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 231 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 231 283 (accept_3_3 47 231 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 231 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 231 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 231 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 231 283 (accept_3_3 44 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 231 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 231 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 231 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 231 283 (accept_3_3 41 231 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 231 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 231 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 231 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 231 283 (accept_3_3 38 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 231 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 231 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 231 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 231 283 (accept_3_3 35 231 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 231 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 231 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 231 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 231 283 (accept_3_3 32 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 231 283 (Polychromatic418967fa.accept_16_15_7_11_1_3760 31 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 231 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 231 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 231 283 (accept_3_3 29 231 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 231 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 231 283
  (Polychromatic418967fa.accept_19_8_3_17_1_5181 27 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 231 283 (accept_3_3 26 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 231 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 231 283 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 231 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 231 283 (accept_3_3 23 231 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 231 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 231 283 (accept_3_3 20 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 231 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 231 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 231 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 231 283 (accept_3_3 17 231 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 231 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 283
  (Polychromatic418967fa.accept_16_15_7_11_1_3760 15 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 231 283 (accept_3_3 14 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 283 (Polychromatic418967fa.accept_20_13_11_3_1_4509 13 231 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 231 283 (Polychromatic418967fa.accept_8_4_7_3_1_144
  12 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 283 (accept_3_3 11
  231 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 10 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 231 283 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 231 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 283 (accept_3_3 8 231 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 231 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 231 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 231 283 (Polychromatic418967fa.accept_19_6_3_17_1_9472
  6 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 283 (accept_3_3 5
  231 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 231 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 231 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 231 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 283 (accept_3_3 2 231 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 231 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 231 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 283)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 230 283 (Eq.refl Bool.true) (allA_of_3_1 54 230 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 55 229 283 (Eq.refl Bool.true) (allA_succ_of_accept 54 229 283 (Polychromatic418967fa.accept_4_2_1_3_1_27
  54 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 229 283 (accept_3_3 53
  229 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 229 283
  (Polychromatic418967fa.accept_17_1_8_11_1_6471 52 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 229 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 229 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 229 283 (accept_3_3 50 229 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 229 283 (Polychromatic418967fa.accept_21_7_19_10_1_8567 49 229 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 229 283
  (Polychromatic418967fa.accept_17_14_8_11_1_4052 48 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 229 283 (accept_3_3 47 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 229 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 229 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 229 283 (Polychromatic418967fa.accept_28_17_5_3_1_17383 45 229
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 229 283 (accept_3_3 44 229
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 229 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 229 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 229 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 229 283 (accept_3_3 41 229 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 229 283 (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 229 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 229 283
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 39 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 229 283 (accept_3_3 38 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 229 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 229 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 229 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 229 283 (accept_3_3 35 229 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 229 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 229 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 229 283
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 229 283 (accept_3_3 32 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 229 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 229 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 229 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 229 283 (accept_3_3 29 229 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 229 283 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 229 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 229 283
  (Polychromatic418967fa.accept_37_27_7_24_1_17382 27 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 229 283 (accept_3_3 26 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 229 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 25 229 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 229 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907
  24 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 229 283 (accept_3_3 23
  229 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 229 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 229 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 229 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 229 283 (accept_3_3 20 229 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 229 283 (Polychromatic418967fa.accept_17_2_8_11_1_1041 19 229 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 229 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 229 283 (accept_3_3 17 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 229 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 229 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 229 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 229 283 (accept_3_3 14 229 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 229 283 (Polychromatic418967fa.accept_29_13_26_22_1_17381 13 229 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 283
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 229 283 (accept_3_3 11 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 229 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 229 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 229 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 283 (accept_3_3 8 229 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 283 (Polychromatic418967fa.accept_13_7_8_10_1_2663
  7 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 283 (accept_3_3 5 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 229 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 283 (Polychromatic418967fa.accept_19_3_1_17_1_5159 3 229 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 283 (accept_3_3 2 229 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 229 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 228 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 228 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 228 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 228 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 54 228
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 228 283 (accept_3_3 53 228
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 228 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 52 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 228 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 228 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 228 283 (accept_3_3 50 228 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 228 283 (Polychromatic418967fa.accept_14_7_4_3_1_488 49 228 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 228 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 228 283 (accept_3_3 47 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 228 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 228 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 228 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 228 283 (accept_3_3 44 228 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 228 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 228 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 228 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 228 283 (accept_3_3 41 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 228 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 40 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 228 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 228 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 228 283 (accept_3_3 38 228 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 228 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 228 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 228 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 228 283 (accept_3_3 35 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 228 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 228 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 228 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 228 283 (accept_3_3 32 228 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 228 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 228 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 228 283
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 228 283 (accept_3_3 29 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 228 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 228 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 228 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 228 283 (accept_3_3 26 228 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 228 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 228 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 228 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 228 283 (accept_3_3 23 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 228 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 228 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 228 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 228 283 (accept_3_3 20 228 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 228 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 228 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 228 283
  (Polychromatic418967fa.accept_17_1_7_11_1_2892 18 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 228 283 (accept_3_3 17 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 228 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 228 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 228 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 228 283 (accept_3_3 14 228 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 228 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 228 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 228 283
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 228 283 (accept_3_3 11 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 228 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 228 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 228 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 228
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 228 283 (accept_3_3 8 228 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7
  228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 228 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 228 283 (accept_3_3 5 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  228 283 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 228 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 228 283 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 228 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 228 283 (accept_3_3 2 228 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 228 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 227 283 (Eq.refl Bool.true) (allA_of_3_1 57
  227 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 226 283 (Eq.refl Bool.true) (allA_succ_of_accept 57
  226 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 226 283 (accept_3_3 56 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 226 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 226 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 226 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 226 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 226 283 (accept_3_3 53 226 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 226 283 (Polychromatic418967fa.accept_9_7_1_4_1_217
  52 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 226 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 226 283 (accept_3_3 50 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 226 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 226 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 226 283 (accept_3_3 47 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 226 283 (Polychromatic418967fa.accept_21_4_16_10_1_10019 46 226 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 226 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 226 283 (accept_3_3 44 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 226 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 226 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 226 283 (accept_3_3 41 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 226 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 226 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 226 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 226 283 (accept_3_3 38 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 226 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 226 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 226 283 (accept_3_3 35 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 226 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 226 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 226 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 226 283 (accept_3_3 32 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 226 283 (Polychromatic418967fa.accept_22_9_6_19_1_6439 31 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 226 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 226 283 (accept_3_3 29 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 226 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 226 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 226 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 226 283 (accept_3_3 26 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 226 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 226 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 226 283 (accept_3_3 23 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 226 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 226 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 226 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 226 283 (accept_3_3 20 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 226 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 226 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 226 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 226 283 (accept_3_3 17 226 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 226 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 226 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 226 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 226 283 (accept_3_3 14 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 226 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 226 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 226 283 (accept_3_3 11 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 226 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 226 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 226 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 226 283 (accept_3_3 8 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  226 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 226 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 226 283 (accept_3_3 5 226 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 226 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 226 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 226 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 226 283 (accept_3_3 2 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  226 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 226 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 226 283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 225 283
  (Eq.refl Bool.true) (allA_succ_of_accept 58 225 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 225 283
  (Polychromatic418967fa.accept_10_7_5_3_1_542 57 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 225 283 (accept_3_3 56 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 225 283 (Polychromatic418967fa.accept_20_15_5_3_1_1953 55 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 225 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 225 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 225 283 (accept_3_3 53 225 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 225 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 225 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 225 283 (accept_3_3 50 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 225 283 (Polychromatic418967fa.accept_17_15_4_11_1_6515 49 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 225 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 225 283 (accept_3_3 47 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 225 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 225 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 225 283
  (Polychromatic418967fa.accept_13_6_4_10_1_660 45 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 225 283 (accept_3_3 44 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 225 283 (Polychromatic418967fa.accept_21_1_15_10_1_11607 43 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 225 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 225 283 (accept_3_3 41 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 225 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 225 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 225 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 225 283 (accept_3_3 38 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 225 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 225 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 225 283 (accept_3_3 35 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 225 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 225 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 225 283 (accept_3_3 32 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 225 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 225 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 225 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 225 283 (accept_3_3 29 225 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 283
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 225 283 (accept_3_3 26 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 225 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 225 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 283 (accept_3_3 23 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 225 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 283
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 21 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 225 283 (accept_3_3 20 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 225 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 225 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 225 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 283 (accept_3_3 17 225 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 225 283 (accept_3_3 14 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 225 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 225 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 225 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 283 (accept_3_3 11 225 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 225 283 (accept_3_3 8 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  225 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 225 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 225 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 283 (accept_3_3 5 225 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 225 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 283
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 225 283 (accept_3_3 2 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  225 283 (Polychromatic418967fa.accept_13_1_4_10_1_622 1 225 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 225 283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 224 283
  (Eq.refl Bool.true) (allA_of_3_1 60 224 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 223 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 60 223 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 223 283 (accept_3_3 59 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 223 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 223 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 223 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 223 283 (accept_3_3 56 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 223 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 223 283 (Polychromatic418967fa.accept_17_3_2_11_1_1895 54 223 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 223 283 (accept_3_3 53 223 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 223 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 223 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 223 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 223 283 (accept_3_3 50 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 223 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 223 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 223 283 (accept_3_3 47 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 223 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 223 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 223 283
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 223 283 (accept_3_3 44 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 223 283 (Polychromatic418967fa.accept_17_9_2_11_1_4042 43 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 223 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 223 283 (accept_3_3 41 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 223 283 (Polychromatic418967fa.accept_18_4_7_13_1_3303 40 223 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 223 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 223 283 (accept_3_3 38 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 223 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 223 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 223 283 (accept_3_3 35 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 223 283 (Polychromatic418967fa.accept_13_8_2_10_1_652 34 223 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 223 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 223 283 (accept_3_3 32 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 223 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 31 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 223 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 283 (accept_3_3 29 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 223 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 223 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 283
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 223 283 (accept_3_3 26 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 223 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 223 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 283 (accept_3_3 23 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 283 (Polychromatic418967fa.accept_18_4_7_13_1_3303 22 223 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 223 283 (accept_3_3 20 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 223 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 223 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 283 (accept_3_3 17 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 223 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 283 (accept_3_3 14 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 283 (Polychromatic418967fa.accept_23_13_16_7_1_2722 13 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 223 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 283 (accept_3_3 11 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 223 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 223 283 (accept_3_3 8 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  223 283 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 223 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 283 (accept_3_3 5 223 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 223 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 283 (accept_3_3 2 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 223 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 222 283
  (Eq.refl Bool.true) (allA_succ_of_accept 61 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 222 283
  (Polychromatic418967fa.accept_11_5_2_8_1_866 60 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 222 283 (accept_3_3 59 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 222 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 222 283 (accept_3_3 56 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 222 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 222 283
  (Polychromatic418967fa.accept_19_16_13_17_1_12066 54 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 222 283 (accept_3_3 53 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 222 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 222 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 222 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 222 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 222 283 (accept_3_3 50 222 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 222 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 222 283 (accept_3_3 47 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 222 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 222 283 (accept_3_3 44 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 222 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 222 283
  (Polychromatic418967fa.accept_17_8_1_11_1_4004 42 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 222 283 (accept_3_3 41 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 222 283 (Polychromatic418967fa.accept_15_10_12_13_1_2585 40 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 222 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 222 283 (accept_3_3 38 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 222 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 222 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 222 283 (accept_3_3 35 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 222 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 222 283 (accept_3_3 32 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 222 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 222 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 222 283 (accept_3_3 29 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 222 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 222 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 222 283 (accept_3_3 26 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 222 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 222 283
  (Polychromatic418967fa.accept_13_11_1_10_1_648 24 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 222 283 (accept_3_3 23 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 222 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 222 283 (accept_3_3 20 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 222 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 222 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 222 283 (accept_3_3 17 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 222 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 222 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 222 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 222 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 222 283 (accept_3_3 14 222 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 222 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 222 283 (accept_3_3 11 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 222 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 283 (accept_3_3 8 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 283
  (Polychromatic418967fa.accept_19_6_13_17_1_8015 6 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 222 283 (accept_3_3 5 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  222 283 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 222 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 222 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 283 (accept_3_3 2 222 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 222 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 221 283 (Eq.refl Bool.true)
  (allA_of_3_1 63 221 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 220 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 220 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 220 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 220 283 (accept_3_3 62 220 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 220 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 61 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 220 283
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 220 283 (accept_3_3 59 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 220 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 220 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 220 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 220 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 220 283 (accept_3_3 56 220 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 220 283 (Polychromatic418967fa.accept_8_7_4_3_1_156
  55 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 220 283
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 220 283 (accept_3_3 53 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 220 283 (Polychromatic418967fa.accept_16_4_12_11_1_2650 52 220 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 220 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51
  220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 220 283 (accept_3_3 50
  220 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 220 283
  (Polychromatic418967fa.accept_14_7_10_3_1_1034 49 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 220 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 220 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 220 283 (accept_3_3 47 220 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 220 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 220 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 220 283 (accept_3_3 44 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 220 283 (Polychromatic418967fa.accept_18_7_4_13_1_3315 43 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 220 283 (Polychromatic418967fa.accept_15_12_10_13_1_4497 42 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 220 283 (accept_3_3 41 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 220 283 (Polychromatic418967fa.accept_16_8_12_11_1_3697 40 220
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 220 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 220 283 (accept_3_3 38 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 220 283 (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 220 283 (Polychromatic418967fa.accept_16_4_12_11_1_2650 36 220 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 220 283 (accept_3_3 35 220 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 220 283 (Polychromatic418967fa.accept_12_10_4_7_1_948
  34 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 220 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 220 283 (accept_3_3 32 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 220 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 220 283 (Polychromatic418967fa.accept_25_5_20_8_1_17380 30 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 220 283 (accept_3_3 29 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 220 283 (Polychromatic418967fa.accept_13_2_12_10_1_2649 28 220
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 220 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 220 283 (accept_3_3 26 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 220 283 (Polychromatic418967fa.accept_18_7_4_13_1_3315 25 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 220 283 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 220 283 (accept_3_3 23 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 220 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 220
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 220 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 220 283 (accept_3_3 20 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 220 283 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 220 283 (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 220 283 (accept_3_3 17 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 220 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 220
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 220 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 220 283 (accept_3_3 14 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 220 283 (Polychromatic418967fa.accept_14_13_10_3_1_1037 13 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 220 283 (Polychromatic418967fa.accept_15_12_10_13_1_4497 12 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 220 283 (accept_3_3 11 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 220 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 220
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 220 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 220 283 (accept_3_3 8 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  220 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 220 283 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 220 283 (accept_3_3 5 220 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 220 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 220
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 220 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 220 283 (accept_3_3 2 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  220 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 220 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 220 283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 219 283
  (Eq.refl Bool.true) (allA_succ_of_accept 64 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 219 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 63 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 219 283 (accept_3_3 62 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 219 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 219 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 219 283 (accept_3_3 59 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 219 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 219 283 (accept_3_3 56 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 219 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 219 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 219 283 (accept_3_3 53 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 219 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 219 283 (accept_3_3 50 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 219 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 49 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 219 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 219 283 (accept_3_3 47 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 219 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 219 283 (accept_3_3 44 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 219 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 219 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 219 283 (accept_3_3 41 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 219 283
  (Polychromatic418967fa.accept_17_5_15_11_1_3978 39 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 219 283 (accept_3_3 38 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 219 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 219 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 219 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 219 283 (accept_3_3 35 219 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34
  219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 219 283 (accept_3_3 32 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 219 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 219 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 30 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 219 283 (accept_3_3 29 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 219 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 219 283 (accept_3_3 26 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 219 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 219 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 283 (accept_3_3 23 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 219 283 (accept_3_3 20 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 219 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 219 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 283 (accept_3_3 17 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 219 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 219 283 (accept_3_3 14 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 219 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 219 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 283 (accept_3_3 11 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 283
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 219 283 (accept_3_3 8 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  219 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 219 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 283 (accept_3_3 5 219 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 219 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 283
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 219 283 (accept_3_3 2 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  219 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 219 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 219 283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 218 283
  (Eq.refl Bool.true) (allA_of_3_1 66 218 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 217 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 66 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 217 283 (accept_3_3 65 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 217 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 64 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 217 283
  (Polychromatic418967fa.accept_17_12_13_11_1_2910 63 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 217 283 (accept_3_3 62 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 217 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 217 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 217 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 217 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 217 283 (accept_3_3 59 217 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 217 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 217 283 (accept_3_3 56 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 217 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 217 283 (accept_3_3 53 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 217 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 217 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 51 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 217 283 (accept_3_3 50 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 217 283 (Polychromatic418967fa.accept_17_15_13_11_1_4031 49 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 217 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 217 283 (accept_3_3 47 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 217 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 217 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 217 283 (accept_3_3 44 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 217 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 217 283 (accept_3_3 41 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 217 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 40 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 217 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 217 283 (accept_3_3 38 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 217 283 (Polychromatic418967fa.accept_16_5_9_11_1_3762 37 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 217 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 217 283 (accept_3_3 35 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 217 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 217 283 (accept_3_3 32 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 217 283 (Polychromatic418967fa.accept_24_7_1_19_1_2203 31 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 283 (accept_3_3 29 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 217 283 (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 217 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 217 283
  (Polychromatic418967fa.accept_13_1_9_10_1_625 27 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 217 283 (accept_3_3 26 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 217 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 217 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 283 (accept_3_3 23 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 217 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 217 283 (accept_3_3 20 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 217 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 283 (accept_3_3 17 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 217 283 (accept_3_3 14 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 217 283 (Polychromatic418967fa.accept_21_13_7_10_1_8599 13 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 217 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 283 (accept_3_3 11 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 283
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 283 (accept_3_3 8 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 283 (accept_3_3 5 217 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 217 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 283 (accept_3_3 2 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 283 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 217 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 216
  283 (Eq.refl Bool.true) (allA_succ_of_accept 67 216 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 216 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 216 283
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 216 283 (accept_3_3 65 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 216 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 64 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 216 283 (Polychromatic418967fa.accept_13_11_8_10_1_676 63 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 216 283 (accept_3_3 62 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 216 283 (Polychromatic418967fa.accept_16_13_8_11_1_4785 61 216
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 216 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 216 283 (accept_3_3 59 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 216 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 216 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 57 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 216 283 (accept_3_3 56 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 216 283 (Polychromatic418967fa.accept_25_5_16_8_1_8647 55 216
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 216 283
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 54 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 216 283 (accept_3_3 53 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 216 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 216 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 216 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 216 283 (accept_3_3 50 216 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 216 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 49 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 216 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 216 283 (accept_3_3 47 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 216 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 216 283 (Polychromatic418967fa.accept_16_13_8_11_1_4785 45 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 216 283 (accept_3_3 44 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 216 283 (Polychromatic418967fa.accept_13_4_8_10_1_671 43 216
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 216 283
  (Polychromatic418967fa.accept_25_17_16_8_1_15755 42 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 216 283 (accept_3_3 41 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 216 283 (Polychromatic418967fa.accept_17_6_12_11_1_5231 40 216 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 216 283 (Polychromatic418967fa.accept_7_4_6_3_1_271
  39 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 216 283 (accept_3_3 38
  216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 216 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 216 283 (Polychromatic418967fa.accept_16_4_8_11_1_5961 36 216 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 216 283 (accept_3_3 35 216 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 216 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 34 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 216 283
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 216 283 (accept_3_3 32 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 216 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 216 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 216 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 216 283 (accept_3_3 29 216 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 216 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 216 283
  (Polychromatic418967fa.accept_10_7_6_3_1_927 27 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 216 283 (accept_3_3 26 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 216 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 216 283 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 216 283 (accept_3_3 23 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 283 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 216
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 216 283
  (Polychromatic418967fa.accept_16_5_8_11_1_9582 21 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 216 283 (accept_3_3 20 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 216 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 216 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 216 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 216 283 (accept_3_3 17 216 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 216 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 216 283
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 216 283 (accept_3_3 14 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 216 283 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 216 283 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 216 283 (accept_3_3 11 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 216 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 216
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 216 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 216 283 (accept_3_3 8 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  216 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 216 283 (Polychromatic418967fa.accept_17_6_12_11_1_5231 6 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 283 (accept_3_3 5 216 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 216 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 216 283
  (Polychromatic418967fa.accept_16_3_8_11_1_2714 3 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 216 283 (accept_3_3 2 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  216 283 (Polychromatic418967fa.accept_22_1_18_19_1_3294 1 216 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 216 283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 215
  283 (Eq.refl Bool.true) (allA_of_3_1 69 215 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 214 283
  (Eq.refl Bool.true) (allA_succ_of_accept 69 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 214 283 (accept_3_3 68 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 214 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 67 214
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 214 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 214 283 (accept_3_3 65 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 214 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 214 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 214 283 (accept_3_3 62 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 214 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 214 283 (accept_3_3 59 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 214 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 58 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 214 283 (accept_3_3 56 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 214 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 214 283
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 214 283 (accept_3_3 53 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 214 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 214 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 214 283 (accept_3_3 50 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 214 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 214 283 (accept_3_3 47 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 214 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 214 283 (accept_3_3 44 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 214 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 214 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 214 283 (accept_3_3 41 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 214 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 214 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 214 283 (accept_3_3 38 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 214 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 214 283 (accept_3_3 35 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 214 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 214 283 (accept_3_3 32 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 214 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 214 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 214 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 214 283 (accept_3_3 29 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 214 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 214 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 214 283 (accept_3_3 26 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 214 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 214 283 (accept_3_3 23 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 214 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 214 283 (accept_3_3 20 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 214 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 214 283
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 214 283 (accept_3_3 17 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 214 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 214 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 214 283 (accept_3_3 14 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 214 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 214 283 (accept_3_3 11 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 214 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 214 283 (accept_3_3 8 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 214 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 214 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 214 283 (accept_3_3 5 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  214 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 214 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 214 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 214 283 (accept_3_3 2 214 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 214 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 214 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 214
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 213 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 213 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 213 283 (Polychromatic418967fa.accept_13_4_5_10_1_1247 69 213
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 213 283 (accept_3_3 68 213
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 213 283
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 213 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 213 283 (accept_3_3 65 213 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 213 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 213 283 (Polychromatic418967fa.accept_12_3_9_7_1_472
  63 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 213 283 (accept_3_3 62
  213 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 213 283
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 213 283 (Polychromatic418967fa.accept_13_8_5_10_1_2701 60 213 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 213 283 (accept_3_3 59 213 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 213 283 (Polychromatic418967fa.accept_9_3_6_4_1_210
  57 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 213 283 (accept_3_3 56
  213 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 283
  (Polychromatic418967fa.accept_9_1_6_4_1_49 55 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 213 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 213 283 (accept_3_3 53 213 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 213 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 213 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371
  51 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 213 283 (accept_3_3 50
  213 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 283
  (Polychromatic418967fa.accept_19_11_4_17_1_2617 49 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 213 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 213 283 (accept_3_3 47 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 213 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 213 283
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 213 283 (accept_3_3 44 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 213 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 283 (accept_3_3 41 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 213 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 213 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 213 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 213 283 (accept_3_3 38 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 213 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 213 283 (Polychromatic418967fa.accept_17_2_9_11_1_4057 36 213 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 283 (accept_3_3 35 213 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 213 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 213 283
  (Polychromatic418967fa.accept_21_12_3_10_1_8575 33 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 213 283 (accept_3_3 32 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 213 283 (Polychromatic418967fa.accept_15_1_3_13_1_2548 31 213 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 213 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 283 (accept_3_3 29 213 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 213 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 213 283 (accept_3_3 26 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 213 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 213 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 213 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 283 (accept_3_3 23 213 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 213 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 213 283 (accept_3_3 20 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 213 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 283 (accept_3_3 17 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 213 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 213 283 (accept_3_3 14 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 213 283 (Polychromatic418967fa.accept_19_13_4_17_1_5166 13 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 213 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 283 (accept_3_3 11 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 213 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 283
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 213 283 (accept_3_3 8 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  213 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 213 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 283 (accept_3_3 5 213 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 213 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 213 283 (accept_3_3 2 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  213 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 213 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 213 283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72
  212 283 (Eq.refl Bool.true) (allA_of_3_1 72 212 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 211 283
  (Eq.refl Bool.true) (allA_succ_of_accept 72 211 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 211 283 (accept_3_3 71 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 211 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 70 211
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 211 283
  (Polychromatic418967fa.accept_17_1_7_11_1_2892 69 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 211 283 (accept_3_3 68 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 211 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 211 283 (Polychromatic418967fa.accept_19_9_2_17_1_10805 66 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 211 283 (accept_3_3 65 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 211 283 (Polychromatic418967fa.accept_17_13_7_11_1_3985 64 211
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 211 283
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 211 283 (accept_3_3 62 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 211 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 211 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 211 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 211 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 211 283 (accept_3_3 59 211 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 211 283 (Polychromatic418967fa.accept_7_2_1_3_1_102
  58 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 211 283
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 57 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 211 283 (accept_3_3 56 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 211 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 211 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 211 283 (Polychromatic418967fa.accept_7_5_1_3_1_103
  54 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 211 283 (accept_3_3 53
  211 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 211 283
  (Polychromatic418967fa.accept_10_2_1_3_1_233 52 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 211 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 211 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 211 283 (accept_3_3 50 211 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 211 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 211 283
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 211 283 (accept_3_3 47 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 211 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 211 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 45 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 211 283 (accept_3_3 44 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 211 283 (Polychromatic418967fa.accept_19_5_2_17_1_8066 43 211
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 211 283
  (Polychromatic418967fa.accept_10_2_1_3_1_233 42 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 211 283 (accept_3_3 41 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 211 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 211 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 211 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 211 283 (accept_3_3 38 211 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 211 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 283
  (Polychromatic418967fa.accept_21_15_1_10_1_8592 36 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 211 283 (accept_3_3 35 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 211 283 (Polychromatic418967fa.accept_19_15_2_17_1_5163 34 211 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 211 283 (Polychromatic418967fa.accept_7_5_1_3_1_103
  33 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 211 283 (accept_3_3 32
  211 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 211 283
  (Polychromatic418967fa.accept_16_15_3_11_1_5997 31 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 211 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 211 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 211 283 (accept_3_3 29 211 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 211 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 283
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 211 283 (accept_3_3 26 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 211 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 211 283 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 283 (accept_3_3 23 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 22 211
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 283
  (Polychromatic418967fa.accept_22_21_13_19_1_11339 21 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 211 283 (accept_3_3 20 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 211 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 211 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 211 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 283 (accept_3_3 17 211 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 283 (Polychromatic418967fa.accept_7_2_1_3_1_102
  16 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 283
  (Polychromatic418967fa.accept_13_2_3_10_1_658 15 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 283 (accept_3_3 14 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 283 (Polychromatic418967fa.accept_17_13_7_11_1_3985 13 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 211 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 283 (accept_3_3 11 211 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 211 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 283 (accept_3_3 8 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 6 211 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 283 (accept_3_3 5 211 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 211 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 283
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 3 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 283 (accept_3_3 2 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 283 (Polychromatic418967fa.accept_17_1_7_11_1_2892 1 211 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  210 283 (Eq.refl Bool.true) (allA_succ_of_accept 73 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 210 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 210 283
  (Polychromatic418967fa.accept_17_4_6_11_1_1030 72 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 210 283 (accept_3_3 71 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 210 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 210 283 (accept_3_3 68 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 210 283 (Polychromatic418967fa.accept_19_10_1_17_1_6595 67 210 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 210 283
  (Polychromatic418967fa.accept_19_9_1_17_1_3879 66 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 210 283 (accept_3_3 65 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 210 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 210 283 (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 210 283 (accept_3_3 62 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 210 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 210 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 210 283 (accept_3_3 59 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 210 283 (Polychromatic418967fa.accept_13_6_2_10_1_1240 58 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 210 283 (accept_3_3 56 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 210 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 210 283
  (Polychromatic418967fa.accept_16_6_2_11_1_7132 54 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 210 283 (accept_3_3 53 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 210 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 210 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 210 283 (accept_3_3 50 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 210 283
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 48 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 210 283 (accept_3_3 47 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 210 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 210 283 (accept_3_3 44 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 210 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 210 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 210 283 (accept_3_3 41 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 210 283 (Polychromatic418967fa.accept_24_16_18_19_1_17379 40 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 210 283 (Polychromatic418967fa.accept_16_7_2_11_1_931 39 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 210 283 (accept_3_3 38 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 210 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 210 283
  (Polychromatic418967fa.accept_24_12_18_19_1_15823 36 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 210 283 (accept_3_3 35 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 210 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 210 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 210 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 210 283 (accept_3_3 32 210 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 210 283 (Polychromatic418967fa.accept_13_5_2_10_1_248
  31 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 210 283
  (Polychromatic418967fa.accept_17_13_6_11_1_4014 30 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 210 283 (accept_3_3 29 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 210 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 210 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 210 283 (Polychromatic418967fa.accept_20_7_10_3_1_949 27 210
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 210 283 (accept_3_3 26 210
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  25 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 210 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 210 283 (accept_3_3 23 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 210 283 (Polychromatic418967fa.accept_16_6_2_11_1_7132 22 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 210 283 (accept_3_3 20 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 210 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 210 283
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 210 283 (accept_3_3 17 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 210 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 210 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 210 283 (accept_3_3 14 210 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 210 283
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 210 283 (accept_3_3 11 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 210 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 210 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 210 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 283 (accept_3_3 8 210 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 210 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 210 283 (accept_3_3 5 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  210 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 210 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 210 283 (Polychromatic418967fa.accept_13_3_2_10_1_2697 3 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 283 (accept_3_3 2 210 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 210 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 209 283 (Eq.refl
  Bool.true) (allA_of_3_1 75 209 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 208 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 208 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 208 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 208 283 (accept_3_3 74 208 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 208 283 (Polychromatic418967fa.accept_18_1_10_13_1_500 73 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 208 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 208 283 (accept_3_3 71 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 208 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 208 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 208 283 (accept_3_3 68 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 208 283 (Polychromatic418967fa.accept_19_10_18_17_1_8030 67 208 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 208 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 208 283 (accept_3_3 65 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 208 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 208 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 208 283 (accept_3_3 62 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 208 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 208 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 208 283 (accept_3_3 59 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 208 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 208 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 208 283 (accept_3_3 56 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 208 283 (Polychromatic418967fa.accept_10_5_8_3_1_229 55 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 208 283
  (Polychromatic418967fa.accept_19_16_18_17_1_6570 54 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 208 283 (accept_3_3 53 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 208 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 208 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 208 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 208 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 208 283 (accept_3_3 50 208 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 208 283
  (Polychromatic418967fa.accept_17_15_4_11_1_6515 49 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 208 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 208 283 (accept_3_3 47 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 208 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 208 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 208 283 (accept_3_3 44 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 208 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 208 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 208 283 (accept_3_3 41 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 208 283 (Polychromatic418967fa.accept_17_6_4_11_1_4072 40 208 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 208 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 208 283 (accept_3_3 38 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 208 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 208 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 208 283 (accept_3_3 35 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 208 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 208 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 208 283 (accept_3_3 32 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 208 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 208 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 208 283 (accept_3_3 29 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 208 283 (Polychromatic418967fa.accept_21_7_19_10_1_8567 28 208 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 208 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 208 283 (accept_3_3 26 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 208 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 208 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 208 283 (accept_3_3 23 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 208 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 208 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 208 283 (accept_3_3 20 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 208 283 (Polychromatic418967fa.accept_14_5_12_3_1_3397 19 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 208 283 (Polychromatic418967fa.accept_20_18_8_3_1_9071 18 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 208 283 (accept_3_3 17 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 208 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 208 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 208 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 208 283 (accept_3_3 14 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 208 283 (Polychromatic418967fa.accept_19_13_18_17_1_5141 13 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 208 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 208 283 (accept_3_3 11 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 208 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 208
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 208 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 208 283 (accept_3_3 8 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  208 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 208 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 208 283 (accept_3_3 5 208 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 208 283 (Polychromatic418967fa.accept_18_4_10_13_1_5883 4 208 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 208 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 208 283 (accept_3_3 2 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  208 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 208 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 208 283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  77 207 283 (Eq.refl Bool.true) (allA_succ_of_accept 76 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 207 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 75 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 207 283 (accept_3_3 74 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 207 283 (Polychromatic418967fa.accept_13_8_12_10_1_4414 73 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 207 283 (Polychromatic418967fa.accept_13_7_12_10_1_640 72 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 207 283 (accept_3_3 71 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 207 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 207 283 (accept_3_3 68 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 207 283 (Polychromatic418967fa.accept_13_2_12_10_1_2649 67 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 207 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 66 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 207 283 (accept_3_3 65 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 207 283
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 207 283 (accept_3_3 62 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 207 283 (Polychromatic418967fa.accept_13_9_12_10_1_242 61 207 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 207 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 207 283 (accept_3_3 59 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58
  207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 207 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 207 283 (accept_3_3 56 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 207 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 207 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 207 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 207 283 (accept_3_3 53 207 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 207 283
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 51 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 207 283 (accept_3_3 50 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 207 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 207 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 207 283 (accept_3_3 47 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 207 283
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 207 283 (accept_3_3 44 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 207 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 207 283 (Polychromatic418967fa.accept_16_10_15_11_1_3785 42 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 283 (accept_3_3 41 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 207 283
  (Polychromatic418967fa.accept_16_7_15_11_1_951 39 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 207 283 (accept_3_3 38 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 207 283 (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 283 (accept_3_3 35 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 207 283 (accept_3_3 32 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 207 283 (Polychromatic418967fa.accept_15_1_12_13_1_944 31 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 207 283 (Polychromatic418967fa.accept_20_10_7_3_1_16094 30 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 283 (accept_3_3 29 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 207 283 (accept_3_3 26 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 207 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 207 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 207 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 283 (accept_3_3 23 207 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 283
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 207 283 (accept_3_3 20 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 207 283 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 207 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 283 (accept_3_3 17 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 207 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 207 283 (accept_3_3 14 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 207 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 207 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 207 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 283 (accept_3_3 11 207 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 207 283 (accept_3_3 8 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  207 283 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 207 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 283 (accept_3_3 5 207 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 283
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 283 (accept_3_3 2 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  207 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 207 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  78 206 283 (Eq.refl Bool.true) (allA_of_3_1 78 206 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 205 283
  (Eq.refl Bool.true) (allA_succ_of_accept 78 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 205 283 (accept_3_3 77 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 205 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 205 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 205 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 205 283 (accept_3_3 74 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 205 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 205 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 205 283 (accept_3_3 71 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 205 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 205 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 205 283 (accept_3_3 68 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 205 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 67 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 205 283 (accept_3_3 65 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 205 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 205 283
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 205 283 (accept_3_3 62 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 205 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 205 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 205 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 205 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 205 283 (accept_3_3 59 205 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 205 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 205 283 (accept_3_3 56 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 205 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 205 283 (accept_3_3 53 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 205 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 52 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 205 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 205 283 (accept_3_3 50 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 205 283 (Polychromatic418967fa.accept_15_4_10_13_1_2565 49 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 205 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 283 (accept_3_3 47 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 205 283
  (Polychromatic418967fa.accept_19_7_15_17_1_5198 45 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 205 283 (accept_3_3 44 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 205 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 205 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 205 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 283 (accept_3_3 41 205 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 205 283 (Polychromatic418967fa.accept_7_5_2_3_1_106
  40 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 205 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 205 283 (accept_3_3 38 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 205 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 205 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 205 283 (accept_3_3 35 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 205 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 205 283 (accept_3_3 32 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 205 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 205 283 (accept_3_3 29 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 205 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 205 283 (accept_3_3 26 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 205 283 (Polychromatic418967fa.accept_17_8_1_11_1_4004 25 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 205 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 283 (accept_3_3 23 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 205 283 (accept_3_3 20 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 205 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 283 (accept_3_3 17 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 205 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 283 (accept_3_3 14 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 283 (accept_3_3 11 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 283
  (Polychromatic418967fa.accept_21_9_16_10_1_5371 9 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 283 (accept_3_3 8 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 283 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 283 (accept_3_3 5 205 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 205 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 283 (accept_3_3 2 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 205 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 204 283 (Eq.refl Bool.true) (allA_succ_of_accept 79 204 283 (Polychromatic418967fa.accept_7_2_1_3_1_102
  79 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 204 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 78 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 204 283 (accept_3_3 77 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 204 283 (Polychromatic418967fa.accept_24_4_12_19_1_12489 76 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 204 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 204 283 (accept_3_3 74 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 204 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 204 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 204 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 204 283 (accept_3_3 71 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 204 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 204 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 69 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 204 283 (accept_3_3 68 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 204 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 204 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 204 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 204 283 (accept_3_3 65 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 204 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 204 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 204 283 (accept_3_3 62 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 204 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 204 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 204 283 (accept_3_3 59 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 204 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 204 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 204 283 (accept_3_3 56 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 204 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 204 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 204 283 (accept_3_3 53 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 204 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 204 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 204 283 (accept_3_3 50 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 204 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 204 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 204 283 (accept_3_3 47 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 204 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 204 283 (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 204 283 (accept_3_3 44 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 204 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 204 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 204 283
  (Polychromatic418967fa.accept_16_10_12_11_1_346 42 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 204 283 (accept_3_3 41 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 204 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 204 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 204 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 204 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 204 283 (accept_3_3 38 204 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 204 283 (Polychromatic418967fa.accept_7_2_1_3_1_102
  37 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 204 283
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 204 283 (accept_3_3 35 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 204 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 204 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 204 283 (accept_3_3 32 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 204 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 204 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 204 283 (accept_3_3 29 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 204 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 204 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 283 (accept_3_3 26 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 204 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 283
  (Polychromatic418967fa.accept_16_8_12_11_1_3697 24 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 204 283 (accept_3_3 23 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 204 283 (Polychromatic418967fa.accept_15_7_9_13_1_3451 22 204 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 204 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 204 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 283 (accept_3_3 20 204 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 283 (Polychromatic418967fa.accept_7_5_1_3_1_103
  19 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 204 283 (accept_3_3 17 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 204 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 204 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 283 (accept_3_3 14 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 283 (Polychromatic418967fa.accept_20_13_4_3_1_14612 13 204 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 204 283 (accept_3_3 11 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 204 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 204 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 283 (accept_3_3 8 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 283
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 204 283 (accept_3_3 5 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  204 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 204 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 204 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 283 (accept_3_3 2 204 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 204 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 203 283 (Eq.refl
  Bool.true) (allA_of_3_1 81 203 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 202 283 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 202 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 202 283 (accept_3_3 80 202 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 202 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 202 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  78 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 202 283 (accept_3_3 77
  202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 202 283
  (Polychromatic418967fa.accept_12_4_10_7_1_149 76 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 202 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 202 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 202 283 (accept_3_3 74 202 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 202 283 (Polychromatic418967fa.accept_7_2_6_3_1_100
  72 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 202 283 (accept_3_3 71
  202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 202 283
  (Polychromatic418967fa.accept_20_10_2_3_1_7425 70 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 202 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 202 283 (accept_3_3 68 202 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 202 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 202 283
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 202 283 (accept_3_3 65 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 202 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 202 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 202 283 (accept_3_3 62 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 202 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 202 283 (accept_3_3 59 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 202 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 202 283 (accept_3_3 56 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 202 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 55 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 202 283
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 54 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 202 283 (accept_3_3 53 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 202 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 202 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 202 283 (accept_3_3 50 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 202 283
  (Polychromatic418967fa.accept_19_10_12_17_1_1506 48 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 202 283 (accept_3_3 47 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 202 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 202 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 202 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 202 283 (accept_3_3 44 202 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 202 283
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 43 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 202 283 (Polychromatic418967fa.accept_13_3_7_10_1_668 42 202 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 202 283 (accept_3_3 41 202 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 202 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 202 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 202 283 (accept_3_3 38 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 202 283 (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 202 283 (accept_3_3 35 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 202 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 202
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 202 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 202 283 (accept_3_3 32 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 202 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 202 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 202 283 (accept_3_3 29 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 202 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 202 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 202 283 (accept_3_3 26 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 202 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 202 283 (accept_3_3 23 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 202 283 (Polychromatic418967fa.accept_17_5_15_11_1_3978 22 202
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 202 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 202 283 (accept_3_3 20 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 202 283 (Polychromatic418967fa.accept_20_19_2_3_1_4486 19 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 202 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 202 283 (accept_3_3 17 202 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 202 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 202 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 202 283 (accept_3_3 14 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 202 283 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 202 283 (accept_3_3 11 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 202 283 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 202
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 202 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 202 283 (accept_3_3 8 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  202 283 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 202 283 (Polychromatic418967fa.accept_15_6_7_13_1_1666 6 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 202 283 (accept_3_3 5 202 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 202 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 202 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 202 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 202 283 (accept_3_3 2 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  202 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 202 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 202 283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 201 283 (Eq.refl Bool.true) (allA_succ_of_accept 82 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27
  82 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 201 283
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 81 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 201 283 (accept_3_3 80 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 201 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 201 283 (accept_3_3 77 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 201 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 201 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 75 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 201 283 (accept_3_3 74 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 201 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 201 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 201 283 (accept_3_3 71 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 201 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 201 283 (accept_3_3 68 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 201 283 (Polychromatic418967fa.accept_13_2_6_10_1_2703 67 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 201 283 (accept_3_3 65 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 201 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 201 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 201 283 (accept_3_3 62 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 201 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 201 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 201 283 (accept_3_3 59 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 201 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 201 283 (accept_3_3 56 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 201 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 201 283 (accept_3_3 53 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 201 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 201 283 (accept_3_3 50 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 201 283 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 201 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 201 283 (accept_3_3 47 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 201 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 201 283
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 45 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 201 283 (accept_3_3 44 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 201 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 201 283 (accept_3_3 41 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 283
  (Polychromatic418967fa.accept_11_6_3_8_1_843 39 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 201 283 (accept_3_3 38 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 201 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 201 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 283 (accept_3_3 35 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 201 283 (accept_3_3 32 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 201 283 (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 283 (accept_3_3 29 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 283
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 201 283 (accept_3_3 26 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 201 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 201 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 283 (accept_3_3 23 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 283
  (Polychromatic418967fa.accept_16_5_9_11_1_3762 21 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 201 283 (accept_3_3 20 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 201 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 283 (accept_3_3 17 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 201 283 (accept_3_3 14 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 201 283 (Polychromatic418967fa.accept_19_13_11_17_1_5152 13 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 283 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 283 (accept_3_3 11 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 201 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 201 283 (accept_3_3 8 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  201 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 201 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 283 (accept_3_3 5 201 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 201 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 201 283 (accept_3_3 2 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  201 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 201 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 201 283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 84 200 283 (Eq.refl Bool.true) (allA_of_3_1 84 200 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 85 199 283 (Eq.refl Bool.true) (allA_succ_of_accept 84 199 283 (Polychromatic418967fa.accept_8_4_7_3_1_144
  84 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 199 283 (accept_3_3 83
  199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 199 283
  (Polychromatic418967fa.accept_16_2_7_11_1_1698 82 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 199 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 81 199 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 199 283 (accept_3_3 80 199 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 199 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 199 283 (Polychromatic418967fa.accept_9_6_1_4_1_474
  78 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 199 283 (accept_3_3 77
  199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 199 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 76 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 199 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 199 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 199 283 (accept_3_3 74 199 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 199 283 (Polychromatic418967fa.accept_13_8_4_10_1_4358 73 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 199 283
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 72 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 199 283 (accept_3_3 71 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 199 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 199 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 199 283 (accept_3_3 68 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 199 283 (Polychromatic418967fa.accept_16_3_7_11_1_1723 67 199 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 199 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 199 283 (accept_3_3 65 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 199 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 64 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 199 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 199 283 (accept_3_3 62 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 199 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 199 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 199 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 60 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 199 283 (accept_3_3 59 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 199 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 58 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 199 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 199 283 (accept_3_3 56 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 199 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 55 199 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 199 283
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 199 283 (accept_3_3 53 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 199 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 199 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 199 283 (accept_3_3 50 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 199 283 (Polychromatic418967fa.accept_19_11_9_17_1_8038 49 199 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 199 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 199 283 (accept_3_3 47 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 199 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 46 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 199 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 283 (accept_3_3 44 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 199 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 199 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 199 283 (accept_3_3 41 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 199 283 (Polychromatic418967fa.accept_13_1_4_10_1_622 40 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 199 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 283 (accept_3_3 38 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 283 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 199 283 (accept_3_3 35 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 199 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 199 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 283 (accept_3_3 32 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 283 (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 199 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 199 283 (accept_3_3 29 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 199 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 199 283 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 283 (accept_3_3 26 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 199 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 283 (accept_3_3 23 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 283 (Polychromatic418967fa.accept_20_2_19_3_1_10530 22 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 283 (accept_3_3 20 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 283 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 283
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 283 (accept_3_3 17 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 283 (accept_3_3 14 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 283 (Polychromatic418967fa.accept_17_13_12_11_1_2947 13 199 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 283
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 283 (accept_3_3 11 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 283 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 283 (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 283 (accept_3_3 8 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 199 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 283 (accept_3_3 5 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 199 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 283 (accept_3_3 2 199 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 283 (Polychromatic418967fa.accept_13_1_4_10_1_622 1 199 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 198 283
  (Eq.refl Bool.true) (allA_succ_of_accept 85 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 198 283
  (Polychromatic418967fa.accept_13_6_3_10_1_698 84 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 198 283 (accept_3_3 83 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 198 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 198 283 (accept_3_3 80 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 198 283 (Polychromatic418967fa.accept_19_3_8_17_1_5213 79 198 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 198 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 198 283 (accept_3_3 77 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 198 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 198 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 198 283 (accept_3_3 74 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 198 283
  (Polychromatic418967fa.accept_13_7_3_10_1_656 72 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 198 283 (accept_3_3 71 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 198 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 70 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 198 283 (accept_3_3 68 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 198 283 (Polychromatic418967fa.accept_13_2_3_10_1_658 67 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 198 283
  (Polychromatic418967fa.accept_10_6_8_3_1_930 66 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 198 283 (accept_3_3 65 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 198 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 198 283 (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 198 283 (accept_3_3 62 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 198 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 198 283
  (Polychromatic418967fa.accept_19_3_8_17_1_5213 60 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 198 283 (accept_3_3 59 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 198 283 (Polychromatic418967fa.accept_13_6_3_10_1_698 58 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 198 283 (accept_3_3 56 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 198 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 198 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 198 283 (accept_3_3 53 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 198 283 (Polychromatic418967fa.accept_16_4_6_11_1_3753 52 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 198 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 198 283 (accept_3_3 50 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 198 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 198 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 198 283 (accept_3_3 47 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 198 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 198 283 (accept_3_3 44 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 198 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 198 283
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 42 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 198 283 (accept_3_3 41 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 198 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 198 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 198 283 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 198
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 198 283 (accept_3_3 38 198
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9
  37 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 198 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 198 283 (accept_3_3 35 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 198 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 198 283 (accept_3_3 32 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 283 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 198 283
  (Polychromatic418967fa.accept_19_11_8_17_1_12103 30 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 198 283 (accept_3_3 29 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 198 283 (Polychromatic418967fa.accept_13_2_3_10_1_658 28 198 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 198 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 198 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 283 (accept_3_3 26 198 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 283
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 198 283 (accept_3_3 23 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 198 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 198 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 198 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 283 (accept_3_3 20 198 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 283 (Polychromatic418967fa.accept_7_5_2_3_1_106
  19 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 283
  (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 198 283 (accept_3_3 17 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 198 283 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 198 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 283 (accept_3_3 14 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 198 283 (accept_3_3 11 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 198 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 10 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 283 (accept_3_3 8 198 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 283 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 198 283 (accept_3_3 5 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  198 283 (Polychromatic418967fa.accept_16_4_6_11_1_3753 4 198 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 198 283 (Polychromatic418967fa.accept_16_3_6_11_1_2718 3 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 283 (accept_3_3 2 198 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 198 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 197 283
  (Eq.refl Bool.true) (allA_of_3_1 87 197 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 196 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 196 283 (accept_3_3 86 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 196 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 85 196 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 196 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 196 283 (accept_3_3 83 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 196 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 196 283 (accept_3_3 80 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 196 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 196 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 196 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 196 283 (accept_3_3 77 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 196 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 76 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 196 283 (accept_3_3 74 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 196 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 196 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 196 283
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 72 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 196 283 (accept_3_3 71 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 196 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 196 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 196 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 196 283 (accept_3_3 68 196 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 196 283 (Polychromatic418967fa.accept_10_7_6_3_1_927
  67 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 196 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 196 283 (accept_3_3 65 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 196 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 196 283 (accept_3_3 62 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 196 283 (Polychromatic418967fa.accept_13_9_1_10_1_647 61 196 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 196 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 196 283 (accept_3_3 59 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 196 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 196 283 (accept_3_3 56 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 196 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 196 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 196 283
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 196 283 (accept_3_3 53 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 196 283 (Polychromatic418967fa.accept_22_8_20_19_1_8153 52 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 196 283 (accept_3_3 50 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 196 283 (Polychromatic418967fa.accept_10_9_6_3_1_545 49 196 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 196 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 196 283 (accept_3_3 47 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 196 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 196 283 (accept_3_3 44 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 196 283 (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 196 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 196 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 196 283 (accept_3_3 41 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 196 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 196 283 (accept_3_3 38 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 196 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 196 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 196 283
  (Polychromatic418967fa.accept_17_2_9_11_1_4057 36 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 196 283 (accept_3_3 35 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 196 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 196 283 (accept_3_3 32 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 196 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 196 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 196 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 196 283 (accept_3_3 29 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 196 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 196 283 (accept_3_3 26 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 196 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 196 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 196 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 196 283 (accept_3_3 23 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 196 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 196 283 (accept_3_3 20 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 196 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 196 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 196 283
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 196 283 (accept_3_3 17 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 196 283 (Polychromatic418967fa.accept_21_16_7_10_1_8601 16 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 196 283 (accept_3_3 14 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 196 283 (Polychromatic418967fa.accept_19_13_6_17_1_12101 13 196 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 196 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 196 283 (accept_3_3 11 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 196 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 283 (accept_3_3 8 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 196 283 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 196 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 196 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 196 283 (accept_3_3 5 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  196 283 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 196 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 196 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 283 (accept_3_3 2 196 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 196 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 195 283
  (Eq.refl Bool.true) (allA_succ_of_accept 88 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 195 283
  (Polychromatic418967fa.accept_10_7_5_3_1_542 87 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 195 283 (accept_3_3 86 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 195 283 (Polychromatic418967fa.accept_20_5_15_3_1_4516 85 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 195 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 84 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 195 283 (accept_3_3 83 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 195 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 195 283 (accept_3_3 80 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 195 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 195 283 (Polychromatic418967fa.accept_10_8_5_3_1_543 78 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 195 283 (accept_3_3 77 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 195 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 195 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 75 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 195 283 (accept_3_3 74 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 195 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 195 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 195 283 (accept_3_3 71 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 195 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 69 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 195 283 (accept_3_3 68 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 195 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 195 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 195 283 (accept_3_3 65 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 195 283
  (Polychromatic418967fa.accept_16_15_3_11_1_5997 63 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 195 283 (accept_3_3 62 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 195 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 195 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 195 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 195 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 195 283 (accept_3_3 59 195 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58
  195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 195 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 195 283 (accept_3_3 56 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 195 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 195 283 (Polychromatic418967fa.accept_16_6_3_11_1_3751 54 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 195 283 (accept_3_3 53 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 195 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 195 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 195 283 (accept_3_3 50 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 195 283 (Polychromatic418967fa.accept_19_11_5_17_1_2620 49 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 195 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 283 (accept_3_3 47 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 195 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 195 283 (accept_3_3 44 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 195 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 195 283 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 283 (accept_3_3 41 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 195 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 195 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 195 283 (accept_3_3 38 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 195 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 195 283 (Polychromatic418967fa.accept_17_2_8_11_1_1041 36 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 283 (accept_3_3 35 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 195 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 195 283 (accept_3_3 32 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 195 283 (Polychromatic418967fa.accept_16_15_3_11_1_5997 31 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 195 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 283 (accept_3_3 29 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 283
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 195 283 (accept_3_3 26 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 195 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 195 283 (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 283 (accept_3_3 23 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 195 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 195 283 (accept_3_3 20 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 195 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 195 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 283 (accept_3_3 17 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 195 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 283
  (Polychromatic418967fa.accept_16_15_3_11_1_5997 15 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 283 (accept_3_3 14 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 195 283 (Polychromatic418967fa.accept_25_13_20_8_1_6726 13 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 283 (Polychromatic418967fa.accept_9_3_6_4_1_210
  12 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 283 (accept_3_3 11
  195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 10 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 195 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 195 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 283 (accept_3_3 8 195 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 195 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 283 (Polychromatic418967fa.accept_16_6_3_11_1_3751
  6 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 283 (accept_3_3 5
  195 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 283
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 195 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 195 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 195 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 283 (accept_3_3 2 195 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 195 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 195 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 194 283
  (Eq.refl Bool.true) (allA_of_3_1 90 194 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 193 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 90 193 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 193 283 (accept_3_3 89 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 193 283 (Polychromatic418967fa.accept_19_12_3_17_1_5182 88 193 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 193 283
  (Polychromatic418967fa.accept_22_21_17_19_1_15910 87 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 193 283 (accept_3_3 86 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 193 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 193 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 193 283 (Polychromatic418967fa.accept_19_8_3_17_1_5181 84 193
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 193 283 (accept_3_3 83 193
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 193 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 193 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 81 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 193 283 (accept_3_3 80 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 193 283 (Polychromatic418967fa.accept_13_1_11_10_1_1258 79 193 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 193 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 193 283 (accept_3_3 77 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 193 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 193 283 (Polychromatic418967fa.accept_24_3_1_19_1_15818 75 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 193 283 (accept_3_3 74 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 193 283 (Polychromatic418967fa.accept_13_8_11_10_1_636 73 193
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 193 283
  (Polychromatic418967fa.accept_17_4_6_11_1_1030 72 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 193 283 (accept_3_3 71 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 193 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 193 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 193 283 (accept_3_3 68 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 193 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 67 193 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 193 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 193 283 (accept_3_3 65 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 193 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 193 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 193 283 (accept_3_3 62 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 193 283 (Polychromatic418967fa.accept_20_1_13_3_1_11838 61 193
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 193 283
  (Polychromatic418967fa.accept_13_8_11_10_1_636 60 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 193 283 (accept_3_3 59 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 193 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 193 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 193 283 (accept_3_3 56 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 193 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 193 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 193 283 (accept_3_3 53 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 193 283 (Polychromatic418967fa.accept_19_14_3_17_1_6558 52 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 193 283 (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 283 (accept_3_3 50 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 193 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 193
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 193 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 193 283 (accept_3_3 47 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 193 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 193 283 (Polychromatic418967fa.accept_27_18_4_13_1_5900 45 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 283 (accept_3_3 44 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 193 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 283 (accept_3_3 41 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 283 (Polychromatic418967fa.accept_13_1_11_10_1_1258 40 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 193 283 (Polychromatic418967fa.accept_17_5_6_11_1_3974 39 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 283 (accept_3_3 38 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 283 (Polychromatic418967fa.accept_21_16_4_10_1_14506 37
  193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 283 (accept_3_3 35 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 193 283 (Polychromatic418967fa.accept_19_14_3_17_1_6558 33 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 283 (accept_3_3 32 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 283 (Polychromatic418967fa.accept_16_15_1_11_1_3747 31 193
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 283 (accept_3_3 29 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 283 (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 283 (accept_3_3 26 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 283
  (Polychromatic418967fa.accept_19_5_3_17_1_6557 24 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 283 (accept_3_3 23 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 283 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 283 (accept_3_3 20 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 283 (Polychromatic418967fa.accept_21_19_4_10_1_3914 19 193
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 283 (accept_3_3 17 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 283 (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 283 (accept_3_3 14 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 283
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 193 283 (accept_3_3 11 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 193 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 193 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 283 (Polychromatic418967fa.accept_24_9_1_19_1_941 9 193 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 283 (accept_3_3 8 193 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 283 (Polychromatic418967fa.accept_14_7_11_3_1_5365
  7 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 283
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 283 (accept_3_3 5 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 283 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 193 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 283 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 283 (accept_3_3 2 193 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 193 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 192 283
  (Eq.refl Bool.true) (allA_succ_of_accept 91 192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 192 283
  (Polychromatic418967fa.accept_11_2_5_8_1_470 90 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 192 283 (accept_3_3 89 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 192 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 192 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 192 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 192 283 (accept_3_3 86 192 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 192 283 (Polychromatic418967fa.accept_10_5_2_3_1_239 85 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 192 283
  (Polychromatic418967fa.accept_17_16_5_11_1_7830 84 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 192 283 (accept_3_3 83 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 192 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 192 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 81 192
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 192 283 (accept_3_3 80 192
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 192 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 79 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 192 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 192 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 192 283 (accept_3_3 77 192 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 192 283 (Polychromatic418967fa.accept_14_6_10_3_1_1038 76 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 192 283
  (Polychromatic418967fa.accept_10_5_2_3_1_239 75 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 192 283 (accept_3_3 74 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 192 283 (Polychromatic418967fa.accept_19_15_2_17_1_5163 72 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 192 283 (accept_3_3 71 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 192 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 192 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 192 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 192 283 (accept_3_3 68 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 192 283 (Polychromatic418967fa.accept_17_16_5_11_1_7830 67 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 192 283 (Polychromatic418967fa.accept_17_15_5_11_1_6468 66 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 192 283 (accept_3_3 65 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 192 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 192 283
  (Polychromatic418967fa.accept_14_7_10_3_1_1034 63 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 192 283 (accept_3_3 62 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 192 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 192 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 192 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 192 283 (accept_3_3 59 192 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 192 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 58 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 192 283
  (Polychromatic418967fa.accept_11_2_5_8_1_470 57 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 192 283 (accept_3_3 56 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 192 283 (Polychromatic418967fa.accept_19_16_2_17_1_8049 54 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 192 283 (accept_3_3 53 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 192 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 192 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 192 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 192 283 (accept_3_3 50 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 192 283 (Polychromatic418967fa.accept_14_7_10_3_1_1034 49 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 192 283 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 192 283 (accept_3_3 47 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 192 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 192 283
  (Polychromatic418967fa.accept_10_5_2_3_1_239 45 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 192 283 (accept_3_3 44 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 192 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 192 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 192 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 192 283 (accept_3_3 41 192 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 283 (Polychromatic418967fa.accept_15_10_12_13_1_2585 40 192 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 192 283
  (Polychromatic418967fa.accept_18_3_12_13_1_3307 39 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 192 283 (accept_3_3 38 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 192 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 192 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 192
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 192 283 (accept_3_3 35 192
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 34 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 192 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 192 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 192 283 (accept_3_3 32 192 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 192 283 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 192 283
  (Polychromatic418967fa.accept_20_10_12_3_1_6003 30 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 192 283 (accept_3_3 29 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 192 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 192 283 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 192
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 192 283 (accept_3_3 26 192
  283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 283
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 192 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 192 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 192 283 (accept_3_3 23 192 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 192 283 (Polychromatic418967fa.accept_19_3_2_17_1_6574 22 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 192 283
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 192 283 (accept_3_3 20 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 192 283 (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 192 283 (accept_3_3 17 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 192 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 192 283 (accept_3_3 14 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 192 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 192 283 (Polychromatic418967fa.accept_19_12_2_17_1_5210 12 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 283 (accept_3_3 11 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 192 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 283
  (Polychromatic418967fa.accept_19_9_2_17_1_10805 9 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 192 283 (accept_3_3 8 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  192 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 192 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 192 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 283 (accept_3_3 5 192 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 283 (Polychromatic418967fa.accept_19_4_2_17_1_3870 4 192 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 283
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 192 283 (accept_3_3 2 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  192 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 192 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 192
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 191 283
  (Eq.refl Bool.true) (allA_of_3_1 93 191 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 190 283 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 190 283 (accept_3_3 92 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 190 283 (Polychromatic418967fa.accept_15_1_10_13_1_939 91 190 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 190 283
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 90 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 190 283 (accept_3_3 89 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 190 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 190 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 190 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 190 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 190 283 (accept_3_3 86 190 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 190 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 84 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 190 283 (accept_3_3 83 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 190 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 190 283 (accept_3_3 80 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 190 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 190 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 78 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 190 283 (accept_3_3 77 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 190 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 190 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 190 283 (accept_3_3 74 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 190 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 190 283 (accept_3_3 71 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 190 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 190 283 (accept_3_3 68 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 190 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 190 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 190 283 (accept_3_3 65 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 190 283 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 190 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 190 283 (accept_3_3 62 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 190 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 190 283 (accept_3_3 59 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 190 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 190 283 (accept_3_3 56 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 190 283 (Polychromatic418967fa.accept_18_1_10_13_1_500 55 190 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 190 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 190 283 (accept_3_3 53 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 190 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 190 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 190 283 (accept_3_3 50 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 190 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 190 283 (accept_3_3 47 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 190 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 190 283 (accept_3_3 44 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 190 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 190 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 190 283 (accept_3_3 41 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 190 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 190 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 190 283 (accept_3_3 38 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 190 283
  (Polychromatic418967fa.accept_17_2_3_11_1_2919 36 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 190 283 (accept_3_3 35 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 190 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 190 283 (accept_3_3 32 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 190 283 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 190 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 190 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 190 283 (accept_3_3 29 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 190 283 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 190 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 190 283 (accept_3_3 26 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 190 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 190 283 (accept_3_3 23 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 190 283 (Polychromatic418967fa.accept_18_4_10_13_1_5883 22 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 190 283 (accept_3_3 20 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 190 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 190 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 190 283 (accept_3_3 17 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 190 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 190 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 190 283 (accept_3_3 14 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 190 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 190 283 (accept_3_3 11 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 190 283 (Polychromatic418967fa.accept_17_10_3_11_1_6482 10 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 190 283 (accept_3_3 8 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 190 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 190 283 (accept_3_3 5 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  190 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 190 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 190 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 283 (accept_3_3 2 190 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 190 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 190 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 189
  283 (Eq.refl Bool.true) (allA_succ_of_accept 94 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 189 283
  (Polychromatic418967fa.accept_11_5_2_8_1_866 93 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 189 283 (accept_3_3 92 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 189 283 (Polychromatic418967fa.accept_28_7_21_3_1_9641 91 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 189 283 (accept_3_3 89 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 189 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 189 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 87 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 189 283 (accept_3_3 86 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 189 283 (Polychromatic418967fa.accept_29_27_15_22_1_17378 85 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 189 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 189 283 (accept_3_3 83 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 189 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 189 283
  (Polychromatic418967fa.accept_13_3_7_10_1_668 81 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 189 283 (accept_3_3 80 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 189 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 79 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 189 283 (accept_3_3 77 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 189 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 189 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 75 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 189 283 (accept_3_3 74 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 189 283 (Polychromatic418967fa.accept_13_8_7_10_1_4362 73 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 189 283 (Polychromatic418967fa.accept_16_8_13_11_1_4772 72 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 189 283 (accept_3_3 71 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 189 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 189 283
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 69 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 189 283 (accept_3_3 68 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 189 283 (Polychromatic418967fa.accept_14_11_7_3_1_3416 67 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 189 283 (accept_3_3 65 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 189 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 189 283 (accept_3_3 62 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 189 283 (Polychromatic418967fa.accept_19_4_18_17_1_1511 61 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 189 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 189 283 (accept_3_3 59 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 189 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 189 283
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 57 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 189 283 (accept_3_3 56 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 189 283 (Polychromatic418967fa.accept_13_3_7_10_1_668 55 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 189 283 (accept_3_3 53 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 189 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 189 283 (accept_3_3 50 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 189 283 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 189 283 (Polychromatic418967fa.accept_15_3_9_13_1_1681 48 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 283 (accept_3_3 47 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 189 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 189 283
  (Polychromatic418967fa.accept_19_7_18_17_1_663 45 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 189 283 (accept_3_3 44 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 189 283 (Polychromatic418967fa.accept_13_4_7_10_1_1200 43 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 283 (accept_3_3 41 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 189 283 (accept_3_3 38 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 189 283 (Polychromatic418967fa.accept_15_7_9_13_1_3451 37 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 189 283 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 283 (accept_3_3 35 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 189 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 283
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 33 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 189 283 (accept_3_3 32 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 189 283 (Polychromatic418967fa.accept_19_12_18_17_1_8075 31 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 283 (accept_3_3 29 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 189 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 283
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 189 283 (accept_3_3 26 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 189 283 (Polychromatic418967fa.accept_13_12_7_10_1_2662 25 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 189 283 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 283 (accept_3_3 23 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 189 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 283
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 189 283 (accept_3_3 20 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 189 283 (Polychromatic418967fa.accept_15_4_9_13_1_2582 19 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 283 (accept_3_3 17 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 189 283 (accept_3_3 14 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 189 283 (Polychromatic418967fa.accept_19_13_18_17_1_5141 13 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 283 (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 189 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 283 (accept_3_3 11 189 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 283
  (Polychromatic418967fa.accept_17_9_2_11_1_4042 9 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 189 283 (accept_3_3 8 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  189 283 (Polychromatic418967fa.accept_15_7_9_13_1_3451 7 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 189 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 283 (accept_3_3 5 189 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 283
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 189 283 (accept_3_3 2 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  189 283 (Polychromatic418967fa.accept_19_1_18_17_1_14761 1 189 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 189
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 188
  283 (Eq.refl Bool.true) (allA_of_3_1 96 188 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 187 283
  (Eq.refl Bool.true) (allA_succ_of_accept 96 187 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 96 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 187 283 (accept_3_3 95 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 187 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 94 187 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 187 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 187 283 (accept_3_3 92 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 187 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 91 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 187 283 (Polychromatic418967fa.accept_19_14_16_17_1_6565 90 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 187 283 (accept_3_3 89 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 187 283 (Polychromatic418967fa.accept_21_4_19_10_1_8531 88 187
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 187 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 87 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 187 283 (accept_3_3 86 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 187 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 187 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 84 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 187 283 (accept_3_3 83 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 187 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 187 283
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 81 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 187 283 (accept_3_3 80 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 187 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 187 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 187 283 (accept_3_3 77 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 187 283 (Polychromatic418967fa.accept_10_6_7_3_1_547 76 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 187 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 75 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 187 283 (accept_3_3 74 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 187 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 187 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 187 283 (accept_3_3 71 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 187 283 (Polychromatic418967fa.accept_19_13_16_17_1_5140 70 187 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 187 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 187 283 (accept_3_3 68 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 187 283 (Polychromatic418967fa.accept_13_2_5_10_1_250 67 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 187 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 187 283 (accept_3_3 65 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 187 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 187 283
  (Polychromatic418967fa.accept_25_13_12_8_1_17377 63 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 187 283 (accept_3_3 62 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 187 283 (Polychromatic418967fa.accept_25_11_12_8_1_10557 61 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 187 283 (Polychromatic418967fa.accept_9_6_7_4_1_212
  60 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 187 283 (accept_3_3 59
  187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 187 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 58 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 187 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 187 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 187 283 (accept_3_3 56 187 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 187 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 187 283 (Polychromatic418967fa.accept_10_4_7_3_1_54
  54 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 187 283 (accept_3_3 53
  187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 187 283
  (Polychromatic418967fa.accept_19_14_16_17_1_6565 52 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 187 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 187 283 (accept_3_3 50 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 187 283 (Polychromatic418967fa.accept_21_7_19_10_1_8567 49 187 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 187 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 187 283 (accept_3_3 47 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 187 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 187 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 283 (accept_3_3 44 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 187 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 187 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 187 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 187 283 (accept_3_3 41 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 187 283 (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 187 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 283 (accept_3_3 38 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 187 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 187 283
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 187 283 (accept_3_3 35 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 187 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 34 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 187 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 187 283 (accept_3_3 32 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 283 (Polychromatic418967fa.accept_22_9_11_19_1_14252 31 187 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 187 283 (accept_3_3 29 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 187 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 187 283 (Polychromatic418967fa.accept_19_8_16_17_1_6552 27 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 283 (accept_3_3 26 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 283 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 187
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 283
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 283 (accept_3_3 23 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 283 (accept_3_3 20 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 283
  (Polychromatic418967fa.accept_19_18_16_17_1_2626 18 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 187 283 (accept_3_3 17 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 187 283 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 187 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 187 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 283 (accept_3_3 14 187 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 283
  (Polychromatic418967fa.accept_19_13_16_17_1_5140 13 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 283 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 283 (accept_3_3 11 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 283 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 283
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 283 (accept_3_3 8 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 283 (Polychromatic418967fa.accept_19_7_16_17_1_6567 7 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 283 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 283 (accept_3_3 5 187 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 283 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 187 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 283
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 283 (accept_3_3 2 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 283 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 187 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  186 283 (Eq.refl Bool.true) (allA_succ_of_accept 97 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 186 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 186 283
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 96 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 186 283 (accept_3_3 95 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 186 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 94 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 186 283 (accept_3_3 92 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 186 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 91 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 186 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 90 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 186 283 (accept_3_3 89 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 186 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 88 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 186 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 87 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 186 283 (accept_3_3 86 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 186 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 186 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 84 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 186 283 (accept_3_3 83 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 186 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 82 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 186 283 (accept_3_3 80 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 186 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 79 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 186 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 186 283 (accept_3_3 77 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 186 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 186 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 186 283 (accept_3_3 74 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 186 283
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 72 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 186 283 (accept_3_3 71 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 186 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 186 283 (accept_3_3 68 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 186 283 (Polychromatic418967fa.accept_10_7_6_3_1_927 67 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 186 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 186 283 (accept_3_3 65 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 186 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 186 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 186 283 (accept_3_3 62 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 186 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 186 283
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 60 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 186 283 (accept_3_3 59 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 186 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 186 283 (accept_3_3 56 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 186 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 186 283
  (Polychromatic418967fa.accept_24_6_18_19_1_17376 54 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 186 283 (accept_3_3 53 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 186 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 186 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 186 283 (Polychromatic418967fa.accept_19_13_15_17_1_5199 51
  186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 186 283 (accept_3_3 50
  186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 186 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 186 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 186 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 186 283 (accept_3_3 47 186 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 186 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 186 283 (accept_3_3 44
  186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 186 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 186 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 186 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 186 283 (accept_3_3 41 186 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 186 283 (Polychromatic418967fa.accept_13_1_4_10_1_622 40 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 186 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 186 283 (accept_3_3 38 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 186 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 186 283 (accept_3_3 35 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 186 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 186 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 186 283 (accept_3_3 32 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 186 283 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 186 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 186 283 (accept_3_3 29 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 186 283
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 186 283 (accept_3_3 26 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 186 283 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 186 283 (accept_3_3 23 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 283 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 186 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 186 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 186 283 (accept_3_3 20 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 186 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 186 283 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 186 283 (accept_3_3 17 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 186 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 186 283
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 186 283 (accept_3_3 14 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 186 283 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 186 283 (accept_3_3 11 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 283 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 186 283
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 186 283 (accept_3_3 8 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  186 283 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 186 283 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 186 283 (accept_3_3 5 186 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 283 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 186 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 186 283
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 186 283 (accept_3_3 2 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  186 283 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 186 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 186
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  185 283 (Eq.refl Bool.true) (allA_of_3_1 99 185 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 184 283
  (Eq.refl Bool.true) (allA_succ_of_accept 99 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 184 283 (accept_3_3 98 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 184 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 184 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 184 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 96 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 184 283 (accept_3_3 95 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 184 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 94 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 184 283 (accept_3_3 92 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 184 283 (Polychromatic418967fa.accept_19_15_13_17_1_5172 91 184 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 184 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 90 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 184 283 (accept_3_3 89 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 184 283 (Polychromatic418967fa.accept_17_3_14_11_1_5243 88 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 184 283 (accept_3_3 86 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 184 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 184 283
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 84 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 184 283 (accept_3_3 83 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 184 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 184 283 (accept_3_3 80 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 184 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 79 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 184 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 184 283 (accept_3_3 77 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 184 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 184 283 (accept_3_3 74 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 184 283 (Polychromatic418967fa.accept_13_8_2_10_1_652 73 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 184 283
  (Polychromatic418967fa.accept_19_15_13_17_1_5172 72 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 184 283 (accept_3_3 71 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 184 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 184 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 184 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 184 283 (accept_3_3 68 184 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 184 283 (Polychromatic418967fa.accept_10_7_4_3_1_560
  67 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 184 283
  (Polychromatic418967fa.accept_15_6_4_13_1_403 66 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 184 283 (accept_3_3 65 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 184 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 184 283 (accept_3_3 62 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 184 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 184 283
  (Polychromatic418967fa.accept_13_8_2_10_1_652 60 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 184 283 (accept_3_3 59 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 184 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 184 283 (accept_3_3 56 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 184 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 184 283
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 184 283 (accept_3_3 53 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 184 283 (Polychromatic418967fa.accept_16_4_8_11_1_5961 52 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 184 283 (accept_3_3 50 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 184 283 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 184 283
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 184 283 (accept_3_3 47 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 184 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 184 283 (accept_3_3 44 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 184 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 184 283
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 184 283 (accept_3_3 41 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 184 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 184 283 (accept_3_3 38 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 184 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 184 283
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 184 283 (accept_3_3 35 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 184 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 184 283 (accept_3_3 32 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 184 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 31 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 184 283
  (Polychromatic418967fa.accept_19_11_13_17_1_9466 30 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 184 283 (accept_3_3 29 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 184 283 (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 184 283 (Polychromatic418967fa.accept_6_3_4_1_1_8 27
  184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 184 283 (accept_3_3 26
  184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 184 283
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 25 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 184 283 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 184 283 (accept_3_3 23 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 184 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 184 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 184 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 184 283 (accept_3_3 20 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 184 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 184 283 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 184 283 (accept_3_3 17 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 184 283 (Polychromatic418967fa.accept_13_3_2_10_1_2697 16 184
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 184 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 184 283 (accept_3_3 14 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 184 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 184 283 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 184 283 (accept_3_3 11 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 184 283 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 184 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 184 283 (accept_3_3 8 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  184 283 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 184 283 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 184 283 (accept_3_3 5 184 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 184 283 (Polychromatic418967fa.accept_16_4_8_11_1_5961 4 184 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 184 283
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 184 283 (accept_3_3 2 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  184 283 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 184 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 184
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 183 283 (Eq.refl Bool.true) (allA_succ_of_accept 100 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 183
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 183 283
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 99 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 183 283 (accept_3_3 98 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 183 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 97 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 183 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 183 283 (accept_3_3 95 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 183 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 183 283 (accept_3_3 92 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 183 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 91 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 183 283 (Polychromatic418967fa.accept_19_14_12_17_1_5196 90 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 183 283 (accept_3_3 89 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 183 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 183 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 87 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 183 283 (accept_3_3 86 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 183 283 (Polychromatic418967fa.accept_15_10_3_13_1_4480 85 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 183 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 183 283 (accept_3_3 83 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 183 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 183 283 (accept_3_3 80 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 183 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 183 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 78 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 183 283 (accept_3_3 77 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 183 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 183 283 (accept_3_3 74 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 183 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 183 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 183 283 (accept_3_3 71 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 183 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 183 283 (accept_3_3 68 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 183 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 183 283 (Polychromatic418967fa.accept_16_2_7_11_1_1698 66 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 183 283 (accept_3_3 65 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 183 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 183 283
  (Polychromatic418967fa.accept_13_11_1_10_1_648 63 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 183 283 (accept_3_3 62 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 183 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 183 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 183 283 (accept_3_3 59 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 183 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 183 283 (accept_3_3 56 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 183 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 183 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 183 283 (accept_3_3 53 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 183 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 183 283 (accept_3_3 50 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 183 283 (Polychromatic418967fa.accept_17_15_13_11_1_4031 49 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 283 (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 183 283 (accept_3_3 47 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 183 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 183 283 (accept_3_3 44 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 183 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 183 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 283 (accept_3_3 41 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 283
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 183 283 (accept_3_3 38 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 183 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 183 283 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 283 (accept_3_3 35 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 283
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 183 283 (accept_3_3 32 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 183 283 (Polychromatic418967fa.accept_15_1_3_13_1_2548 31 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 183 283 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 283 (accept_3_3 29 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 283
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 27 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 183 283 (accept_3_3 26 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 183 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 183 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 283 (accept_3_3 23 183 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 283
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 283 (accept_3_3 20 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 183 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 283 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 283 (accept_3_3 17 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 283
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 183 283 (accept_3_3 14 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 183 283 (Polychromatic418967fa.accept_22_13_7_19_1_15931 13 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 283 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 283 (accept_3_3 11 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 183 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 283
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 183 283 (accept_3_3 8 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  183 283 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 183 283 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 283 (accept_3_3 5 183 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 283 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 283
  (Polychromatic418967fa.accept_16_3_7_11_1_1723 3 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 283 (accept_3_3 2 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 283 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 183 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183
  283))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 182 283 (Eq.refl Bool.true) (allA_of_3_1 102 182 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 181
  283 (Eq.refl Bool.true) (allA_succ_of_accept 102 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 181 283 (accept_3_3 101 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 181 283 (Polychromatic418967fa.accept_7_2_6_3_1_100
  100 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 181 283
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 99 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 181 283 (accept_3_3 98 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 181 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 97 181 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 181 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 96 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 181 283 (accept_3_3 95 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 94
  181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 181 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 93 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 181 283 (accept_3_3 92 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 181 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 91 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 181 283 (accept_3_3 89 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 181 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 181 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 87 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 181 283 (accept_3_3 86 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 181 283 (Polychromatic418967fa.accept_13_7_12_10_1_640 85 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 181 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 181 283 (accept_3_3 83 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 181 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 181 283 (accept_3_3 80 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 181 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 181 283 (accept_3_3 77 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 181 283 (Polychromatic418967fa.accept_13_11_12_10_1_2652 76 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 181 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 75 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 181 283 (accept_3_3 74 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 181 283 (Polychromatic418967fa.accept_13_8_12_10_1_4414 73 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 181 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 181 283 (accept_3_3 71 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 181 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 69 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 181 283 (accept_3_3 68 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 181 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 181 283 (accept_3_3 65 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 181 283 (Polychromatic418967fa.accept_18_10_1_13_1_2192 64 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 181 283
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 181 283 (accept_3_3 62 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 181 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 181 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 181 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 181 283 (accept_3_3 59 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 181 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 181 283 (accept_3_3 56 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 181 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 181 283 (accept_3_3 53 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 181 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 181 283 (accept_3_3 50 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 181 283 (Polychromatic418967fa.accept_21_7_13_10_1_8604 49 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 181 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 283 (accept_3_3 47 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 283
  (Polychromatic418967fa.accept_13_6_12_10_1_690 45 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 283 (accept_3_3 44 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 283 (accept_3_3 41 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 283 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 283
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 283 (accept_3_3 38 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 283 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 283 (accept_3_3 35 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 283 (accept_3_3 32 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 283 (Polychromatic418967fa.accept_19_12_10_17_1_5189 31 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 283 (accept_3_3 29 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 283 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 181
  283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 283
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 181 283 (accept_3_3 26 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 181 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 181 283 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 181 283 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 283 (accept_3_3 23 181 283
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 283 (accept_3_3 20 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 283 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 283 (accept_3_3 17 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 283 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 283
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 283 (accept_3_3 14 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 283 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 283 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 283 (accept_3_3 11 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 283
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 283 (accept_3_3 8 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 283 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 283 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 283 (accept_3_3 5 181 283 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 283 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 181 283 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 283
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 283 (accept_3_3 2 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 283 (Polychromatic418967fa.accept_19_1_10_17_1_5188 1 181 283 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181
  283)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_283_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


